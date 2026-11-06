"""네트워크 없이 PR 검토·게시·머지의 SHA/권한 경계와 실패 처리를 검사한다.

사용:  python3 -I scripts/test_pr_review.py
"""

import base64
import copy
import json
import os
from pathlib import Path
import runpy
import tempfile
import unittest
from unittest.mock import patch
from urllib.error import HTTPError

MODULE = runpy.run_path(str(Path(__file__).with_name("pr_review.py")))
SHA = "a" * 40
BASE = "b" * 40
MB = "c" * 40
OTHER = "d" * 40
PR = {"state": "open", "draft": False, "author_association": "OWNER", "node_id": "node",
      "auto_merge": None, "mergeable_state": "blocked",
      "changed_files": 1, "head": {"sha": SHA, "repo": {"full_name": "owner/repo"}},
      "base": {"sha": BASE, "ref": "main"}}
MANIFEST = {"repository": "owner/repo", "number": 1, "sha": SHA, "base_sha": BASE, "merge_base_sha": MB,
            "files": [{"path": "Kuratowski/Proof.lean", "status": "modified"}]}
RESULT = {"sha": SHA, "verdict": "approve", "reviewed_files": ["Kuratowski/Proof.lean"],
          "summary": "검토한 변경에서 차단 문제 없음", "findings": []}
RULES = [{"type": "required_status_checks", "parameters": {
    "strict_required_status_checks_policy": True,
    "required_status_checks": [{"context": "Lean CI", "integration_id": 15368},
                               {"context": "AI review", "integration_id": 15368}]}}]


def ci_run(status="completed", conclusion: "str | None" = "success", run_id=7,
           created="2026-11-06T10:00:00Z", **change):
    run = {"id": run_id, "path": ".github/workflows/ci.yml", "event": "pull_request", "head_sha": SHA,
           "head_repository": {"full_name": "owner/repo"}, "status": status, "conclusion": conclusion,
           "created_at": created}
    run.update(change)
    return run


LEAN_JOB = {"name": "Lean CI", "status": "completed", "conclusion": "success"}


class Clock:
    def __init__(self):
        self.now = 0.0
        self.sleeps = []

    def clock(self):
        return self.now

    def sleep(self, seconds):
        self.sleeps.append(seconds)
        self.now += seconds


class FakeGitHub:
    repo = "owner/repo"
    token = "dummy-token"

    def __init__(self):
        self.pr = copy.deepcopy(PR)
        self.heads = []            # get_pr가 차례로 돌려줄 head SHA (비면 self.pr 그대로)
        self.writes = []
        self.graphql_calls = []
        self.merges = []
        self.merge_codes = []      # merge가 차례로 돌려줄 코드 (비면 200)
        self.rules = copy.deepcopy(RULES)
        self.files = [{"filename": "Kuratowski/Proof.lean", "status": "modified"}]
        self.content_refs = []
        self.runs = [[ci_run()]]   # 확인할 때마다 하나씩 쓴다 (마지막 것은 계속)
        self.jobs = {7: [LEAN_JOB]}
        self.statuses = []
        self.comments = []

    def get_pr(self, number):
        pr = copy.deepcopy(self.pr)
        if self.heads:
            pr["head"]["sha"] = self.heads.pop(0) if len(self.heads) > 1 else self.heads[0]
        return pr

    def graphql(self, query, variables):
        self.graphql_calls.append((query, variables))
        return {}

    def merge(self, number, sha):  # noqa: 실제 응답 처리는 test_github_merge_requires_merged_true
        self.merges.append((number, sha))
        return self.merge_codes.pop(0) if self.merge_codes else 200

    def request(self, path, data=None, method=None):
        if method:
            self.writes.append((path, data, method))
            return {}
        if path.startswith(f"/repos/{self.repo}/rules/branches/main"):
            return self.rules
        if "/compare/" in path:
            return {"merge_base_commit": {"sha": MB}}
        if "/files?" in path:
            return self.files
        if "/contents/" in path:
            self.content_refs.append(path.rsplit("ref=", 1)[1])
            return {"type": "file", "encoding": "base64", "size": 10,
                    "content": base64.b64encode(b"test data\n").decode()}
        if "/comments?" in path:
            return self.comments
        if "/actions/runs?" in path:
            runs = self.runs.pop(0) if len(self.runs) > 1 else self.runs[0]
            return {"workflow_runs": runs}
        if "/actions/runs/" in path and "/jobs" in path:
            run_id = int(path.split("/actions/runs/")[1].split("/")[0])
            return {"jobs": self.jobs.get(run_id, [])}
        if "/statuses?" in path:
            return self.statuses
        raise AssertionError(path)


def in_tmp(fn):
    old = Path.cwd()
    with tempfile.TemporaryDirectory() as tmp:
        try:
            os.chdir(tmp)
            return fn()
        finally:
            os.chdir(old)


def publish(api, manifest=MANIFEST, result=RESULT):
    clock = Clock()
    state = MODULE["publish"](api, 1, manifest, result, clock.clock, clock.sleep)
    return state, clock


def status_writes(api):
    return [d["state"] for p, d, m in api.writes if "/statuses/" in p]


@patch.dict(os.environ, {"RUN_URL": "https://example.invalid/run"})
class ReviewTests(unittest.TestCase):
    def test_validation_and_rejections(self):
        validate = MODULE["validate"]
        self.assertEqual(validate(json.dumps(RESULT), MANIFEST, "success"), RESULT)
        invalid = [{"sha": BASE}, {"verdict": "maybe"}, {"reviewed_files": []},
                   {"summary": " "}, {"summary": "dummy-token"}, {"findings": None},
                   {"findings": [{"path": "Kuratowski/Proof.lean", "reason": "문제"}]},
                   {"verdict": "request_changes", "findings": [{"path": "other", "reason": "문제"}]}]
        for change in invalid:
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate(json.dumps(RESULT | change), MANIFEST, "success", ("dummy-token",))
        with self.assertRaises(ValueError):
            validate(json.dumps(RESULT), MANIFEST, "failure")
        for raw in ["", "null", "[]"]:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                validate(raw, MANIFEST, "success")

    def test_prepare_does_not_write_pr_paths(self):
        api = FakeGitHub()
        api.files = [{"filename": "../../.claude/settings.json", "status": "modified"}]
        files = in_tmp(lambda: (MODULE["prepare"](api, 1),
                                sorted(str(p) for p in Path(".").rglob("*") if p.is_file()))[1])
        self.assertEqual(files, [".review-input/files/0-after.txt", ".review-input/files/0-before.txt",
                                 ".review-input/manifest.json"])

    def test_prepare_reads_before_at_merge_base_and_records_renames(self):
        api = FakeGitHub()
        api.pr["changed_files"] = 2
        api.files = [{"filename": "Kuratowski/Proof.lean", "status": "modified"},
                     {"filename": "docs/moved.yml", "previous_filename": ".github/workflows/ci.yml",
                      "status": "renamed"}]
        manifest = in_tmp(lambda: (MODULE["prepare"](api, 1),
                                   json.loads(Path(".review-input/manifest.json").read_text()))[1])
        self.assertEqual(manifest["merge_base_sha"], MB)
        self.assertEqual(api.content_refs, [MB, SHA, MB, SHA])  # before는 base 끝이 아니라 merge base
        self.assertEqual(manifest["files"][1]["previous_path"], ".github/workflows/ci.yml")
        self.assertEqual(MODULE["protected_changes"](manifest), [".github/workflows/ci.yml"])

    def test_stale_prepare_fails(self):
        api = FakeGitHub()
        changed = copy.deepcopy(PR)
        changed["head"]["sha"] = OTHER

        def run():
            with patch.object(api, "get_pr", side_effect=[copy.deepcopy(PR), changed]):
                with self.assertRaises(ValueError):
                    MODULE["prepare"](api, 1)
            return Path(".review-input/manifest.json").exists()
        self.assertFalse(in_tmp(run))

    def test_pending_disables_auto_merge_and_returns_sha(self):
        api = FakeGitHub()
        api.pr["auto_merge"] = {"merge_method": "squash"}
        self.assertEqual(MODULE["pending"](api, 1), SHA)
        self.assertEqual(len(api.graphql_calls), 1)
        self.assertIn("disablePullRequestAutoMerge", api.graphql_calls[0][0])
        self.assertEqual(api.graphql_calls[0][1], {"id": "node"})
        self.assertEqual(status_writes(api), ["pending"])
        api = FakeGitHub()
        MODULE["pending"](api, 1)
        self.assertEqual(api.graphql_calls, [])
        api.pr["draft"] = True
        with self.assertRaises(ValueError):
            MODULE["pending"](api, 1)

    def test_approve_waits_for_exact_trusted_ci_then_merges(self):
        api = FakeGitHub()
        api.runs = [[], [ci_run(status="in_progress", conclusion=None)], [ci_run()]]
        state, clock = publish(api)
        self.assertEqual(state, "merged")
        self.assertEqual(api.merges, [(1, SHA)])
        self.assertEqual(clock.sleeps, [30, 30])
        self.assertEqual(status_writes(api), ["success"])
        # auto-merge를 예약하지 않는다.
        self.assertFalse(any("enablePullRequestAutoMerge" in q for q, _ in api.graphql_calls))

    def test_request_changes_never_merges_and_disables_auto_merge(self):
        api = FakeGitHub()
        api.pr["auto_merge"] = {"merge_method": "squash"}
        result = RESULT | {"verdict": "request_changes",
                           "findings": [{"path": "Kuratowski/Proof.lean", "reason": "반례"}]}
        state, _ = publish(api, result=result)
        self.assertEqual(state, "rejected")
        self.assertEqual(api.merges, [])
        self.assertEqual(status_writes(api), ["failure"])
        self.assertEqual(len(api.graphql_calls), 1)

    def test_protected_paths_are_never_merged_automatically(self):
        guarded = [".github/workflows/x.yml", "scripts/pr_review.py", "lakefile.toml",
                   "lake-manifest.json", "lean-toolchain", "KuratowskiAudit.lean"]
        for path in guarded + ["rename"]:
            api = FakeGitHub()
            api.pr["auto_merge"] = {"merge_method": "squash"}
            manifest = copy.deepcopy(MANIFEST)
            entry = ({"path": "docs/moved.yml", "previous_path": "scripts/check_blueprint.py", "status": "renamed"}
                     if path == "rename" else {"path": path, "status": "modified"})
            manifest["files"] = [entry]
            result = RESULT | {"reviewed_files": [entry["path"]]}
            with self.subTest(path=path):
                state, _ = publish(api, manifest, result)
                self.assertEqual(state, "guarded")
                self.assertEqual(api.merges, [])
                self.assertEqual(status_writes(api), ["success"])
                self.assertEqual(len(api.graphql_calls), 1)  # 남아 있던 auto-merge도 끈다
                comment = next(d["body"] for p, d, m in api.writes if p.endswith("/comments"))
                self.assertIn("사람이 머지", comment)
        for path in ["Kuratowski/Contract.lean", "blueprint/src/chapters/faces.tex", "scripts_notes.md", "docs/x.md"]:
            with self.subTest(path=path):
                self.assertFalse(MODULE["is_protected"](path))

    def test_untrusted_ci_runs_are_ignored_until_bounded_timeout(self):
        untrusted = [ci_run(path=".github/workflows/other.yml"), ci_run(event="push"),
                     ci_run(head_sha=OTHER), ci_run(head_repository={"full_name": "outsider/repo"}),
                     ci_run(path=".github/workflows/ci.yml.bak")]
        api = FakeGitHub()
        api.runs = [untrusted]
        state, clock = publish(api)
        self.assertEqual(state, "timeout")
        self.assertEqual(api.merges, [])
        self.assertLessEqual(sum(clock.sleeps), 40 * 60)
        self.assertTrue(set(clock.sleeps) == {30})
        self.assertIn("timeout", MODULE["FAILING_STATES"])

    def test_ci_failures_and_latest_run(self):
        cases = {
            "failed run": ([ci_run(conclusion="failure")], {7: [LEAN_JOB]}, "ci_failed"),
            "cancelled run": ([ci_run(conclusion="cancelled")], {7: [LEAN_JOB]}, "ci_failed"),
            "job failed": ([ci_run()], {7: [LEAN_JOB | {"conclusion": "failure"}]}, "ci_failed"),
            "job missing": ([ci_run()], {7: [LEAN_JOB | {"name": "Other"}]}, "ci_failed"),
            "newer failure": ([ci_run(), ci_run(conclusion="failure", run_id=8, created="2026-11-06T11:00:00Z")],
                              {7: [LEAN_JOB], 8: [LEAN_JOB]}, "ci_failed"),
            "newer success": ([ci_run(conclusion="failure"), ci_run(run_id=8, created="2026-11-06T11:00:00Z")],
                              {7: [LEAN_JOB], 8: [LEAN_JOB]}, "merged"),
        }
        for name, (runs, jobs, want) in cases.items():
            api = FakeGitHub()
            api.runs, api.jobs = [runs], jobs
            with self.subTest(case=name):
                state, _ = publish(api)
                self.assertEqual(state, want)
                self.assertEqual(api.merges, [(1, SHA)] if want == "merged" else [])
        self.assertIn("ci_failed", MODULE["FAILING_STATES"])

    def test_head_change_during_wait_stops_without_merge(self):
        api = FakeGitHub()
        api.heads = [SHA, SHA, OTHER]  # publish 확인, 첫 대기, 두 번째 대기에서 바뀜
        api.runs = [[ci_run(status="in_progress", conclusion=None)]]
        state, _ = publish(api)
        self.assertEqual(state, "stale")
        self.assertEqual(api.merges, [])

    def test_merge_responses(self):
        api = FakeGitHub()
        api.merge_codes = [409]
        self.assertEqual(publish(api)[0], "stale")
        api = FakeGitHub()
        api.merge_codes = [405]
        api.pr["mergeable_state"] = "behind"
        self.assertEqual(publish(api)[0], "behind")
        api = FakeGitHub()
        api.merge_codes = [405, 200]
        state, clock = publish(api)
        self.assertEqual(state, "merged")
        self.assertEqual(api.merges, [(1, SHA), (1, SHA)])
        self.assertEqual(clock.sleeps, [30])

    def test_publish_rejects_unprotected_and_ineligible_before_writing(self):
        cases = ["stale", "closed", "draft", "fork", "author", "wrong_pr",
                 "no_rules", "not_strict", "missing_context", "no_integration", "other_integration"]
        for case in cases:
            api = FakeGitHub()
            manifest = copy.deepcopy(MANIFEST)
            if case == "stale": api.pr["head"]["sha"] = BASE
            elif case == "closed": api.pr["state"] = "closed"
            elif case == "draft": api.pr["draft"] = True
            elif case == "fork": api.pr["head"]["repo"]["full_name"] = "outsider/repo"
            elif case == "author": api.pr["author_association"] = "NONE"
            elif case == "wrong_pr": manifest["number"] = 2
            elif case == "no_rules": api.rules = []
            elif case == "not_strict": api.rules[0]["parameters"]["strict_required_status_checks_policy"] = False
            elif case == "missing_context":
                api.rules[0]["parameters"]["required_status_checks"] = [{"context": "Lean CI", "integration_id": 15368}]
            elif case == "no_integration":
                del api.rules[0]["parameters"]["required_status_checks"][1]["integration_id"]
            else: api.rules[0]["parameters"]["required_status_checks"][0]["integration_id"] = 1
            with self.subTest(case=case):
                with self.assertRaises(ValueError):
                    publish(api, manifest)
                self.assertEqual(api.writes, [])
                self.assertEqual(api.merges, [])
                self.assertEqual(api.graphql_calls, [])

    def test_model_text_is_neutralized_in_comment(self):
        api = FakeGitHub()
        result = RESULT | {"verdict": "request_changes", "summary": "@everyone <!-- hidden -->",
                           "findings": [{"path": "Kuratowski/Proof.lean", "reason": "@bob 확인"}]}
        publish(api, result=result)
        body = next(d["body"] for p, d, m in api.writes if p.endswith("/comments"))
        self.assertTrue(body.startswith(MODULE["MARKER"]))
        self.assertEqual(body.count("<!--"), 1)
        self.assertIn("@​everyone", body)
        self.assertIn("@​bob", body)
        self.assertNotIn("@bob", body)

    @patch.dict(os.environ, {"GITHUB_REPOSITORY": "owner/repo", "GITHUB_TOKEN": "dummy-token"})
    def test_github_merge_requires_merged_true(self):
        api = MODULE["GitHub"]()

        def http(code):
            return HTTPError("https://api.github.com/x", code, "error", {}, None)  # type: ignore[arg-type]
        cases = [({"merged": True, "sha": SHA}, 200), ({"merged": False}, ValueError), (None, ValueError),
                 (http(405), 405), (http(409), 409), (http(500), HTTPError)]
        for response, want in cases:
            effect = response if isinstance(response, HTTPError) else None
            with self.subTest(response=response), patch.object(api, "request", return_value=response,
                                                                side_effect=effect) as request:
                if isinstance(want, type):
                    with self.assertRaises(want):
                        api.merge(1, SHA)
                else:
                    self.assertEqual(api.merge(1, SHA), want)
                path, data, method = request.call_args.args
                self.assertEqual((path, data, method),
                                 ("/repos/owner/repo/pulls/1/merge", {"sha": SHA, "merge_method": "squash"}, "PUT"))

    def test_mark_error_only_replaces_own_pending(self):
        mark = MODULE["mark_error"]
        bot = {"login": "github-actions[bot]"}
        cases = [([{"context": "AI review", "state": "pending", "creator": bot}], True),
                 ([{"context": "AI review", "state": "success", "creator": bot},
                   {"context": "AI review", "state": "pending", "creator": bot}], False),
                 ([{"context": "AI review", "state": "pending", "creator": {"login": "someone"}}], False),
                 ([{"context": "Lean CI", "state": "pending", "creator": bot}], False),
                 ([], False)]
        for statuses, want in cases:
            api = FakeGitHub()
            api.statuses = statuses
            with self.subTest(statuses=statuses):
                self.assertEqual(mark(api, SHA), want)
                self.assertEqual(status_writes(api), ["error"] if want else [])
        for bad in ["", "main", SHA + "\n", "A" * 40]:
            with self.subTest(sha=bad), self.assertRaises(ValueError):
                mark(FakeGitHub(), bad)


if __name__ == "__main__":
    unittest.main()

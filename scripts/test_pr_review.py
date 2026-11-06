"""네트워크 없이 PR 검토·게시의 SHA/권한 경계와 실패 처리를 검사한다."""

import base64
import copy
import json
import os
from pathlib import Path
import runpy
import tempfile
import unittest
from unittest.mock import patch

MODULE = runpy.run_path(str(Path(__file__).with_name("pr_review.py")))
SHA = "a" * 40
BASE = "b" * 40
PR = {"state": "open", "draft": False, "author_association": "OWNER", "node_id": "node",
      "changed_files": 1, "head": {"sha": SHA, "repo": {"full_name": "owner/repo"}},
      "base": {"sha": BASE, "ref": "main"}}
MANIFEST = {"repository": "owner/repo", "number": 1, "sha": SHA, "base_sha": BASE,
            "files": [{"path": "proof.lean", "status": "modified"}]}
RESULT = {"sha": SHA, "verdict": "approve", "reviewed_files": ["proof.lean"],
          "summary": "검토한 변경에서 차단 문제 없음", "findings": []}


class FakeGitHub:
    repo = "owner/repo"
    token = "dummy-token"

    def __init__(self):
        self.pr = copy.deepcopy(PR)
        self.writes = []
        self.merges = []
        self.protected = True
        self.file = {"filename": "proof.lean", "status": "modified"}

    def get_pr(self, number):
        return copy.deepcopy(self.pr)

    def request(self, path, data=None, method=None):
        if path == "/graphql":
            rules = [{"pattern": "main", "requiresStatusChecks": True,
                      "requiresStrictStatusChecks": True,
                      "requiredStatusCheckContexts": ["Lean CI", "AI review"]}] if self.protected else []
            return {"data": {"repository": {"branchProtectionRules": {"nodes": rules}}}}
        if method:
            self.writes.append((path, data, method))
            return {}
        if "/files?" in path:
            return [self.file]
        if "/contents/" in path:
            return {"type": "file", "encoding": "base64", "size": 10,
                    "content": base64.b64encode(b"test data\n").decode()}
        if "/comments?" in path:
            return []
        raise AssertionError(path)

    def merge_when_ready(self, number, sha):
        self.merges.append((number, sha))


class ReviewTests(unittest.TestCase):
    def test_validation_and_rejections(self):
        validate = MODULE["validate"]
        self.assertEqual(validate(json.dumps(RESULT), MANIFEST, "success"), RESULT)
        invalid = [{"sha": BASE}, {"verdict": "maybe"}, {"reviewed_files": []},
                   {"summary": " "}, {"summary": "dummy-token"}, {"findings": None},
                   {"findings": [{"path": "proof.lean", "reason": "문제"}]},
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
        api.file["filename"] = "../../.claude/settings.json"
        old = Path.cwd()
        with tempfile.TemporaryDirectory() as tmp:
            try:
                os.chdir(tmp)
                MODULE["prepare"](api, 1)
                files = sorted(str(p) for p in Path(".").rglob("*") if p.is_file())
                self.assertEqual(files, [".review-input/files/0-after.txt", ".review-input/files/0-before.txt",
                                         ".review-input/manifest.json"])
            finally:
                os.chdir(old)

    def test_stale_prepare_fails(self):
        api = FakeGitHub()
        changed = copy.deepcopy(PR)
        changed["head"]["sha"] = "c" * 40
        old = Path.cwd()
        with tempfile.TemporaryDirectory() as tmp:
            try:
                os.chdir(tmp)
                with patch.object(api, "get_pr", side_effect=[copy.deepcopy(PR), changed]):
                    with self.assertRaises(ValueError):
                        MODULE["prepare"](api, 1)
                self.assertFalse(Path(".review-input/manifest.json").exists())
            finally:
                os.chdir(old)

    @patch.dict(os.environ, {"RUN_URL": "https://example.invalid/run"})
    def test_approve_and_request_changes(self):
        api = FakeGitHub()
        MODULE["publish"](api, 1, MANIFEST, RESULT)
        self.assertEqual(api.merges, [(1, SHA)])
        self.assertEqual(api.writes[-1][1]["state"], "success")
        api = FakeGitHub()
        result = RESULT | {"verdict": "request_changes", "findings": [{"path": "proof.lean", "reason": "반례"}]}
        MODULE["publish"](api, 1, MANIFEST, result)
        self.assertEqual(api.merges, [])
        self.assertEqual(api.writes[-1][1]["state"], "failure")

    @patch.dict(os.environ, {"RUN_URL": "https://example.invalid/run"})
    def test_publish_rejects_stale_untrusted_and_unprotected(self):
        for case in ["stale", "closed", "draft", "fork", "author", "protection", "wrong_pr"]:
            api = FakeGitHub()
            manifest = copy.deepcopy(MANIFEST)
            if case == "stale": api.pr["head"]["sha"] = BASE
            elif case == "closed": api.pr["state"] = "closed"
            elif case == "draft": api.pr["draft"] = True
            elif case == "fork": api.pr["head"]["repo"]["full_name"] = "outsider/repo"
            elif case == "author": api.pr["author_association"] = "NONE"
            elif case == "protection": api.protected = False
            else: manifest["number"] = 2
            with self.subTest(case=case), self.assertRaises(ValueError):
                MODULE["publish"](api, 1, manifest, RESULT)
            self.assertEqual(api.writes, [])
            self.assertEqual(api.merges, [])


if __name__ == "__main__":
    unittest.main()

"""장 선택, 누락 검출, 기존 보고서 거부 규칙을 검사한다."""

import json
import os
from pathlib import Path
import runpy
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/save_review.py"
validate = runpy.run_path(str(SCRIPT))["validate_review"]
MAPPING = json.loads((ROOT / ".github/prompts/review-focus.json").read_text())
SHA = "a" * 40


class ReviewTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.old_cwd = Path.cwd()
        os.chdir(self.tmp.name)
        mapping = Path(".github/prompts/review-focus.json")
        mapping.parent.mkdir(parents=True)
        mapping.write_text(json.dumps(MAPPING))
        for file in {f for files in MAPPING.values() for f in files} | {".git/config", ".env"}:
            path = Path(file)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("검사 자료\n")

    def tearDown(self):
        os.chdir(self.old_cwd)
        self.tmp.cleanup()

    def report(self, focus="faces"):
        return {"sha": SHA, "focus": focus, "reviewed_files": MAPPING[focus], "report": "검토 결과"}

    def test_every_focus_and_each_missing_required_file(self):
        for focus, files in MAPPING.items():
            with self.subTest(focus=focus):
                data = self.report(focus)
                self.assertEqual(validate(json.dumps(data), SHA, "success", focus), data)
                for missing in files:
                    partial = data | {"reviewed_files": [f for f in files if f != missing]}
                    with self.assertRaises(ValueError):
                        validate(json.dumps(partial), SHA, "success", focus)

    def test_reject_invalid_results(self):
        data = self.report()
        patches = [
            {"sha": "b" * 40}, {"focus": "easy"}, {"focus": "unknown"},
            {"report": " "}, {"report": "dummy-secret"}, {"reviewed_files": []},
        ]
        for file in [".git/config", ".env", "../outside", "/etc/passwd", "missing", 42]:
            patches.append({"reviewed_files": MAPPING["faces"] + [file]})
        for patch in patches:
            with self.subTest(patch=patch), self.assertRaises(ValueError):
                validate(json.dumps(data | patch), SHA, "success", "faces", ("dummy-secret",))
        for raw in ["", "not-json", "[]", "null"]:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                validate(raw, SHA, "success", "faces")
        with self.assertRaises(ValueError):
            validate(json.dumps(data), SHA, "failure", "faces")

    def test_prepare_rejects_unknown_input_before_writing_outputs(self):
        for focus in ["unknown", "faces\nother=value", "$(touch injected)"]:
            env = os.environ | {"EXPECTED_FOCUS": focus, "GITHUB_OUTPUT": "outputs"}
            result = subprocess.run(["python3", "-I", str(SCRIPT), "--prepare"], env=env,
                                    capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(Path("outputs").exists())
            self.assertFalse(Path("injected").exists())

    def test_prepare_and_save(self):
        for focus in MAPPING:
            env = os.environ | {
                "EXPECTED_FOCUS": focus, "GITHUB_OUTPUT": "outputs",
                "EXPECTED_SHA": SHA, "REVIEW_CONCLUSION": "success",
                "REVIEW_GITHUB_TOKEN": "dummy-github", "REVIEW_OAUTH_TOKEN": "dummy-oauth",
                "GITHUB_STEP_SUMMARY": "summary", "REVIEW_JSON": json.dumps(self.report(focus)),
            }
            Path("outputs").write_text("")
            subprocess.run(["python3", "-I", str(SCRIPT), "--prepare"], env=env, check=True)
            outputs = dict(line.split("=", 1) for line in Path("outputs").read_text().splitlines())
            self.assertEqual(outputs["focus"], focus)
            self.assertEqual(json.loads(outputs["required_files"]), MAPPING[focus])
            subprocess.run(["python3", "-I", str(SCRIPT)], env=env, check=True)
            self.assertEqual(json.loads(Path("review-output/review.json").read_text()), self.report(focus))


if __name__ == "__main__":
    unittest.main()

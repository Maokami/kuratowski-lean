"""`scripts/ci_blueprint_decls.py`의 이름 뽑기 시험.

사용:  python3 -I scripts/ci_test_blueprint_decls.py
"""

import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("ci_blueprint_decls", HERE / "ci_blueprint_decls.py")
assert spec is not None and spec.loader is not None
cbd = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cbd)


def names(text):
    return cbd.lean_names(cbd.clean(text))


class LeanNames(unittest.TestCase):
    def test_multiline_list(self):
        tex = "\\lean{A.b,\n  A.c,\n\n  A.d}\n\\leanok"
        self.assertEqual(names(tex), ["A.b", "A.c", "A.d"])

    def test_comments_are_ignored(self):
        tex = ("% \\lean{Fake.one}\n"
               "\\lean{A.b, % 주석 안의 \\lean{Fake.two}\n"
               "  A.c}  % \\lean{Fake.three}\n")
        self.assertEqual(names(tex), ["A.b", "A.c"])

    def test_escaped_percent_is_not_a_comment(self):
        tex = "50\\% 확률 \\lean{A.b}"
        self.assertEqual(names(tex), ["A.b"])

    def test_leanok_and_other_commands_are_not_names(self):
        tex = "\\leanok \\leanokay{X} \\lean{A.b}\\leanok \\textbackslash lean{Y}"
        self.assertEqual(names(tex), ["A.b"])

    def test_verbatim_is_ignored(self):
        tex = "\\begin{verbatim}\n\\lean{Fake.v}\n\\end{verbatim}\n\\lean{A.b}"
        self.assertEqual(names(tex), ["A.b"])

    def test_macro_definitions_are_not_names(self):
        tex = ("\\newcommand{\\lean}[1]{}\n\\renewcommand\\lean[1]{#1}\n"
               "\\def\\lean{Fake.d}\n\\lean{A.b}")
        self.assertEqual(names(tex), ["A.b"])

    def test_escaped_underscore(self):
        self.assertEqual(names("\\lean{A.b\\_c, A.d_e}"), ["A.b_c", "A.d_e"])

    def test_unclosed_brace_is_an_error(self):
        with self.assertRaises(ValueError):
            names("\\lean{A.b, A.c")

    def test_non_name_is_an_error(self):
        with self.assertRaises(ValueError):
            names("\\lean{A.b c}")


class Inputs(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "chapters").mkdir()

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        (self.root / rel).write_text(text, encoding="utf-8")

    def test_inputs_follow_document_root_and_skip_commented(self):
        self.write("web.tex", "\\input{content}\n% \\input{chapters/dead}\n")
        self.write("content.tex", "\\input{chapters/one}\n\\input{chapters/two.tex}\n")
        # 하위 파일의 \input도 입구 디렉터리 기준으로 푼다 (TeX와 같다).
        self.write("chapters/one.tex", "\\lean{A.one}\n\\input{chapters/inner}\n")
        self.write("chapters/inner.tex", "\\lean{A.inner}\n")
        self.write("chapters/two.tex", "\\lean{A.two}\n")
        self.write("chapters/dead.tex", "\\lean{Fake.dead}\n")
        got = cbd.lean_names(cbd.expand(self.root / "web.tex"))
        self.assertEqual(got, ["A.one", "A.inner", "A.two"])

    def test_same_file_twice_is_not_a_cycle(self):
        self.write("web.tex", "\\input{chapters/x}\n\\input{chapters/x}\n")
        self.write("chapters/x.tex", "\\lean{A.x}\n")
        self.assertEqual(cbd.lean_names(cbd.expand(self.root / "web.tex")), ["A.x", "A.x"])

    def test_cycle_is_an_error(self):
        self.write("web.tex", "\\input{chapters/a}\n")
        self.write("chapters/a.tex", "\\input{chapters/b}\n")
        self.write("chapters/b.tex", "\\input{chapters/a}\n")
        with self.assertRaises(ValueError):
            cbd.expand(self.root / "web.tex")

    def test_missing_input_is_an_error(self):
        self.write("web.tex", "\\input{chapters/none}\n")
        with self.assertRaises(ValueError):
            cbd.expand(self.root / "web.tex")


class Repository(unittest.TestCase):
    def test_repository_blueprint(self):
        got = cbd.lean_names(cbd.expand(cbd.ENTRY))
        self.assertTrue(got)
        self.assertTrue(all(n.startswith("Kuratowski.") for n in got), got)
        # plasTeX 산출물이 있으면 (로컬에서 leanblueprint web을 돌린 뒤) 순서까지 같아야 한다.
        decls = cbd.ROOT / "blueprint" / "lean_decls"
        if decls.is_file():
            self.assertEqual(got, decls.read_text(encoding="utf-8").split())


if __name__ == "__main__":
    unittest.main()

"""블루프린트의 `\\lean{...}` 이름을 TeX·plasTeX 없이 뽑아 `lake exe checkdecls` 입력을 만든다.

CI에서 TeX를 설치하지 않고 블루프린트의 Lean 이름이 실제로 있는지 확인하려고 쓴다.
`blueprint/src/web.tex`(plasTeX 입구)에서 시작해 `\\input`/`\\include`를 따라가므로,
`leanblueprint web`이 `blueprint/lean_decls`를 만들 때 읽는 파일과 범위가 같다.

규칙:
* `%` 주석(`\\%`는 제외)과 verbatim 계열 환경 안의 내용은 무시한다.
* `\\lean{a, b, ...}`의 인자는 여러 줄에 걸칠 수 있고, 쉼표로 나눈 뒤 공백을 지운다.
* `\\leanok`처럼 `\\lean` 뒤에 글자가 이어지는 명령이나, `\\newcommand{\\lean}`처럼 매크로를 정의하는
  자리는 이름으로 치지 않는다.
* 인자 안의 `\\_`는 `_`로 바꾼다.

사용:  python3 -I scripts/ci_blueprint_decls.py --output PATH   # 한 줄에 이름 하나씩 쓴다
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENTRY = ROOT / "blueprint" / "src" / "web.tex"

VERBATIM = re.compile(r"\\begin\{(verbatim\*?|lstlisting|minted|Verbatim)\}.*?\\end\{\1\}", re.S)
INPUT = re.compile(r"\\(?:input|include)\s*\{([^{}]+)\}")
LEAN = re.compile(r"\\lean(?![A-Za-z@])\s*\{")
MACRO_DEF = re.compile(r"\\(?:newcommand|renewcommand|providecommand|def)\s*\{?\s*\\lean(?![A-Za-z@])")


def strip_comments(text):
    """`%`부터 줄 끝까지 지운다. `\\%`처럼 이스케이프된 문자는 남긴다."""
    lines = []
    for line in text.split("\n"):
        out, i = [], 0
        while i < len(line):
            if line[i] == "\\" and i + 1 < len(line):
                out.append(line[i:i + 2])
                i += 2
                continue
            if line[i] == "%":
                break
            out.append(line[i])
            i += 1
        lines.append("".join(out))
    return "\n".join(lines)


def clean(text):
    return VERBATIM.sub("", strip_comments(text))


def expand(path, base=None, stack=()):
    """`\\input`을 재귀로 펼친 본문을 돌려준다 (주석과 verbatim은 먼저 지운다).

    TeX처럼 `\\input` 경로는 포함하는 파일이 아니라 입구 파일의 디렉터리(`base`)를 기준으로 푼다.
    """
    path = path.resolve()
    base = path.parent if base is None else base
    if path in stack:
        raise ValueError(f"\\input 순환: {path}")
    text = clean(path.read_text(encoding="utf-8"))

    def sub(m):
        target = base / m.group(1).strip()
        if target.suffix != ".tex":
            target = target.with_name(target.name + ".tex")
        if not target.is_file():
            raise ValueError(f"\\input 대상이 없습니다: {m.group(1)}")
        return expand(target, base, stack + (path,))

    return INPUT.sub(sub, text)


def lean_names(text):
    """정리된 본문에서 `\\lean{...}`의 이름을 문서 순서대로 뽑는다."""
    names = []
    macro_spans = [m.span() for m in MACRO_DEF.finditer(text)]
    for m in LEAN.finditer(text):
        if any(a <= m.start() < b for a, b in macro_spans):
            continue
        depth, i = 1, m.end()
        while i < len(text) and depth:
            if text[i] == "\\":
                i += 2
                continue
            depth += {"{": 1, "}": -1}.get(text[i], 0)
            i += 1
        if depth:
            raise ValueError("닫히지 않은 \\lean{...}")
        for part in text[m.end():i - 1].split(","):
            name = part.strip().replace("\\_", "_")
            if name:
                if not re.fullmatch(r"[^\s{}\\]+", name):
                    raise ValueError(f"Lean 이름이 아닙니다: {name!r}")
                names.append(name)
    return names


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, help="이름을 한 줄에 하나씩 쓸 파일")
    ap.add_argument("--entry", default=str(ENTRY), help="블루프린트 입구 파일 (기본: web.tex)")
    args = ap.parse_args(argv)
    names = lean_names(expand(Path(args.entry)))
    if not names:
        print("블루프린트에서 \\lean 이름을 하나도 찾지 못했습니다.", file=sys.stderr)
        return 1
    Path(args.output).write_text("".join(n + "\n" for n in names), encoding="utf-8")
    print(f"{args.output}에 {len(names)}개 이름을 썼습니다.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

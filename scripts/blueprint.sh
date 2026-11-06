#!/usr/bin/env bash
# 블루프린트 빌드와 검사를 한 번에 한다.
#   scripts/blueprint.sh          import 목록 검사 → lake build(공리 감사 포함) → 웹 판 → PDF 판
#                                 → checkdecls → 전수 검사
#   scripts/blueprint.sh --quick  PDF 판과 전수 검사를 건너뛴다
#   scripts/blueprint.sh serve    만든 웹 판을 http://127.0.0.1:8000 에서 보여 준다
# 필요: leanblueprint (uv tool install leanblueprint), graphviz, TeX Live (xelatex, kotex)
set -euo pipefail
cd "$(dirname "$0")/.."

# uv tool은 leanblueprint만 PATH에 올린다. 같은 가상환경의 plastex와 TeX Live를 앞에 둔다.
# TeX Live는 연도별 디렉터리 가운데 마지막(가장 최근) 것이 PATH 맨 앞에 온다.
for d in "$HOME/.local/share/uv/tools/leanblueprint/bin" /usr/local/texlive/*/bin/*; do
  if [ -d "$d" ]; then PATH="$d:$PATH"; fi
done
export PATH

mode="${1:-}"
case "$mode" in
  serve) exec python3 -m http.server 8000 --bind 127.0.0.1 --directory blueprint/web ;;
  ""|--quick) ;;
  *) echo "사용법: $0 [--quick|serve]" >&2; exit 2 ;;
esac

# Kuratowski.lean이 Kuratowski/의 모든 파일을 import하는지 본다. 빠진 파일은 빌드도 공리 감사도 되지 않는다.
echo "== import 목록 (mk_all)"
lake exe mk_all --check --lib Kuratowski
echo "== lake build (공리 감사 포함)"
lake build
echo "== 웹 판"
leanblueprint web
if [ "$mode" != --quick ]; then
  echo "== PDF 판"
  leanblueprint pdf
fi
echo "== checkdecls (\\lean 이름이 Lean에 있는지)"
lake exe checkdecls blueprint/lean_decls
echo "   $(grep -c . blueprint/lean_decls)개 이름 확인"
if [ "$mode" != --quick ]; then
  echo "== 전수 검사"
  python3 -I scripts/check_blueprint.py
fi
echo "== 모두 통과"

#!/usr/bin/env bash
# Generate both formats from the same Verso source.
# Requires the repository's Lean/Lake toolchain and a LuaLaTeX installation.
set -euo pipefail
cd "$(dirname "$0")/.."

if [ "$#" -ne 1 ]; then
  echo "Usage: bash scripts/build_book.sh path/to/generate-book" >&2
  exit 2
fi
exe="$1"
if ! command -v lualatex >/dev/null 2>&1; then
  echo "Error: lualatex is not on PATH. Install MacTeX (including LuaTeX-ja and HaranoAji fonts)." >&2
  exit 1
fi

# Verso v4.35.0 emits HTML to _out/html-multi and a complete book to _out/tex/main.tex.
"$exe" --with-tex
test -s _out/html-multi/index.html || { echo "Verso HTML was not generated" >&2; exit 1; }
test -s _out/tex/main.tex || { echo "Verso TeX was not generated" >&2; exit 1; }

# Verso's memoir preamble is not Japanese-aware. Add only the LuaTeX-ja
# setup to the generated TeX; the actual book content is still rendered by Verso.
# memoir and luatexja both declare \printglossary, so neutralize the old definition.
patched="$(mktemp _out/tex/main.tex.XXXXXX)"
trap 'rm -f "$patched"' EXIT
awk '
{
  print
  if (index($0, "\\setmonofont{DejaVu Sans Mono}") != 0) {
    print "\\let\\printglossary\\relax"
    print "\\usepackage{amsmath,amssymb}"
    print "\\usepackage{luatexja-fontspec}"
    print "\\setmainjfont{HaranoAjiMincho}"
    print "\\setsansjfont{HaranoAjiGothic}"
    found = 1
  }
}
END {
  if (!found) {
    print "Could not locate the known Verso v4.35.0 TeX preamble" > "/dev/stderr"
    exit 1
  }
}' _out/tex/main.tex > "$patched"
mv "$patched" _out/tex/main.tex

# Multiple passes resolve the table of contents and document cross-references.
(
  cd _out/tex
  for pass in 1 2 3; do
    echo "LuaLaTeX pass $pass/3"
    lualatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex
  done
)
test -s _out/tex/main.pdf || { echo "LuaLaTeX PDF was not generated" >&2; exit 1; }
cp _out/tex/main.pdf _out/beilinson-book.pdf

# A compatibility link for the previously documented HTML location.
if [ ! -e _out/html ] && [ ! -L _out/html ]; then
  ln -s html-multi _out/html
fi

echo "HTML: _out/html-multi/index.html"
echo "PDF:  _out/beilinson-book.pdf"

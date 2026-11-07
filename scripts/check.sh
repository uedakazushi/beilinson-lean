#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

test -f lean-toolchain
test -f lakefile.lean

echo "Lean toolchain: $(cat lean-toolchain)"
lake --version
lake exe cache get

# This checks the Lean libraries and produces both Verso HTML and LuaLaTeX PDF.
lake build

echo "All requested build commands finished successfully."

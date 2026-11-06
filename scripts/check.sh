#!/usr/bin/env bash
set -euo pipefail

# Run in the root of the repository after installing the pinned Lean toolchain.
# This script intentionally does not run `lake update`.
# Commit the generated lake-manifest.json after the first dependency resolution.

test -f lean-toolchain
test -f lakefile.toml

echo "Lean toolchain: $(cat lean-toolchain)"
lake --version
lake exe cache get
lake build Beilinson
lake build Book
lake build generate-book
lake exe generate-book

echo "All requested build commands finished successfully."

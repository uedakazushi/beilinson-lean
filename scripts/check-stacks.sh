#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../integrations/stacks"
echo "Checking separately pinned Stacks integration"
echo "This is potentially expensive; it is NOT run by scripts/check.sh."
targets=("$@")
if (($# == 0)); then
  targets=(StacksProbe StacksGeometryProbe StacksGenerationProbe StacksOrdinaryProbe)
fi
lake exe cache get
lake build "${targets[@]}"

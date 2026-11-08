#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../integrations/stacks"
echo "Checking separately pinned Stacks integration"
echo "This is potentially expensive; it is NOT run by scripts/check.sh."
targets=("$@")
if (($# == 0)); then
  targets=(StacksProbe StacksGeometryProbe StacksGenerationProbe StacksOrdinaryProbe StacksAlgebraProbe DGAComparison DegreeZeroConeComparison ConcentratedDGA GeometricPerfectProbe ProjectivePerfectProbe KroneckerCompact SheafHomSections ProjectiveLineEnd CoherentDerivedComparison KroneckerBoundedDerived StacksCohomologyProbe StacksBeilinsonProbe OrdinaryBeilinson BoundedBeilinson ProjectiveLineWindow ProjectiveLineBeilinson PositiveWindow CentralDegreeZero OrdinaryBeilinsonLinear MatrixAlgebraComparison FiniteBoundedDerived GeometricMatrixEnd MatrixBeilinson CoherentTensor ExactBoundedEquivalence CoherentTensorBounded PositiveBounded GeometricMatrixLinear FiniteScalarEquivalence PositiveEndBounded TensorDerivedModels ExactFunctorModels)
fi
lake exe cache get
lake build "${targets[@]}"

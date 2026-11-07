# Optional Axiom Stacks integration (2026-11-08)

This separate Lake project audits reusable declarations without adding Stacks to the
production Beilinson/Verso dependency graph.

- Upstream: https://github.com/AxiomMath/Stacks
- Revision: `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`
- Lean and mathlib: v4.35.0 (matching the root project)
- Tier: the imports below are `StacksFrontier`, whose human review is incomplete.
  Local kernel checking does not change that upstream review status.
- The integration-specific `lake-manifest.json` records actual dependency resolution.
  Do not copy it into the root project.

From this directory:

```sh
lake update
lake exe cache get
lake build StacksProbe StacksGeometryProbe StacksGenerationProbe StacksOrdinaryProbe StacksAlgebraProbe DGAComparison
```

Alternatively, from the repository root, `bash scripts/check-stacks.sh` runs these
six targets. Explicit arguments select other targets when they are available.
This script is separate from the production `scripts/check.sh`.

All six targets have built successfully against the pinned package. Their exported
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; none uses
`sorryAx` or a new axiom. None proves the bounded coherent Beilinson equivalence.

| Target | Module suffix under `StacksFrontier` | Checked claim |
|---|---|---|
| `StacksProbe` (default) | `CategoryTheory.Triangulated.ExceptionalCollectionFiniteness` | A finite exceptional sequence generates if total Hom is finite and its right orthogonal detects zero. |
| `StacksGeometryProbe` | `AlgebraicGeometry.ProjKoszulComplex.Exactness` | The coordinate Koszul complex on polynomial Proj is acyclic over any commutative ring, for every twist. |
| `StacksGenerationProbe` | `AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul` | All non-positive twists lie in the thick subcategory of the finite twist sum; orthogonality propagates to them. |
| `StacksOrdinaryProbe` | `Algebra.DifferentialGraded.Module.DegreeZeroTriangulated` | Degree-zero dg modules have the triangulated derived category of ordinary right modules, encoded by the opposite ring. |
| `StacksAlgebraProbe` | `Homology.Perfect.BeilinsonAlgebra` | On the polynomial-matrix Beilinson algebra, compactness is equivalent to finite total cohomology. |
| `DGAComparison` | `Algebra.DifferentialGraded.AlgebraCategory` and `…Module.DegreeZeroAlgebra` | A new adapter lifts an algebra identification with zero differential and degree-zero concentration to a strict dg algebra isomorphism. |

The Koszul import closure contains 92 Stacks modules, Koszul descent 228, the
ordinary-module comparison 53, the polynomial-matrix criterion 96, and the strict
dg adapter 456. Counts
exclude mathlib and are for this revision.
Do not run `lake build Stacks` or import the umbrella module by default.

Further candidates include negative-twist higher-direct-image vanishing (2125
Stacks modules) and an unbounded dg Beilinson equivalence (8353). They are under
separate local validation; see [../../REUSE.md](../../REUSE.md) for exact declarations
and the semantic audits. Higher direct images use a different base-change model
of projective space from the polynomial Proj used by the Koszul probe. The ordinary
module comparison also needs an adapter from the geometric dg algebra to the
specific degree-zero model. Neither type boundary is silently identified here.

The geometric zero-detection hypotheses, matching the positive twist sum of the
book, the ordinary endomorphism algebra, and the bounded coherent restriction
remain to be connected in this project. Promotion to a production dependency
requires recording the exact declarations, assumptions, model comparisons, and
build cost in the reuse ledger.

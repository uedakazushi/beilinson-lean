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

The optional project references the checked production library through `../..`.
Its manifest therefore also records the root package and its pinned Verso dependencies.
Only imported mathematical modules are built for these probes; the production project
still has no Stacks dependency. Existing pinned dependency revisions were preserved.

From this directory:

```sh
lake update
../../scripts/check-stacks.sh
```

Alternatively, from the repository root, `bash scripts/check-stacks.sh` runs these
twenty-two targets. Explicit arguments select other targets when they are available.
This script is separate from the production `scripts/check.sh`.

All twenty-two targets have built successfully against the pinned package. Their exported
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; none uses
`sorryAx` or a new axiom. `ProjectiveLineBeilinson` proves an actual bounded equivalence in dimension one.
`BoundedBeilinson` uses compact ordinary End(E)-modules as its source in all dimensions.

| Target | Module suffix under `StacksFrontier` | Checked claim |
|---|---|---|
| `StacksProbe` (default) | `CategoryTheory.Triangulated.ExceptionalCollectionFiniteness` | A finite exceptional sequence generates if total Hom is finite and its right orthogonal detects zero. |
| `StacksGeometryProbe` | `AlgebraicGeometry.ProjKoszulComplex.Exactness` | The coordinate Koszul complex on polynomial Proj is acyclic over any commutative ring, for every twist. |
| `StacksGenerationProbe` | `AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul` | All non-positive twists lie in the thick subcategory of the finite twist sum; orthogonality propagates to them. |
| `StacksOrdinaryProbe` | `Algebra.DifferentialGraded.Module.DegreeZeroTriangulated` | Degree-zero dg modules have the triangulated derived category of ordinary right modules, encoded by the opposite ring. |
| `StacksAlgebraProbe` | `Homology.Perfect.BeilinsonAlgebra` | On the polynomial-matrix Beilinson algebra, compactness is equivalent to finite total cohomology. |
| `DGAComparison` | `Algebra.DifferentialGraded.AlgebraCategory` and `…Module.DegreeZeroAlgebra` | A new adapter lifts an algebra identification with zero differential and degree-zero concentration to a strict dg algebra isomorphism. |
| `DegreeZeroConeComparison` | `…Module.DegreeZeroTriangulated`, `…Module.ConeSignTransfer`, and `Algebra.DGA.DerivedCategory` | The ordinary right-module comparison is exact for the cone convention, after the shift sign is corrected. |
| `ConcentratedDGA` | The two local adapters above and mathlib triangulated adjunctions | A concentrated dg algebra equals its degree-zero presentation on the same underlying algebra; its derived category has an exact comparison with ordinary right modules in both directions. |
| `GeometricPerfectProbe` | `AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsCompactIsPerfect` and `…Perfect.RegularBoundedCoherentPerfect` | On a qcqs regular scheme, compact objects of D_QCoh have exactly bounded coherent cohomology, at the locally small derived model. |
| `ProjectivePerfectProbe` | The preceding adapter, `…Variety.Projective.RegularProjectiveSpace`, and `…ProjNoetherian.Basic` | Polynomial projective space over every field is regular, including n = 0; compactness is equivalent to bounded coherent cohomology. |
| `KroneckerCompact` | Production `Beilinson.KroneckerPerfect` and `Homology.Perfect.Characterizing` | Right Kronecker complexes are compact/perfect exactly when bounded with finite-dimensional cohomology. This uses the concrete checked algebra, not a geometric End identification. |
| `SheafHomSections` | `AlgebraicGeometry.DerivedGlobalSectionsLinear`, `…DerivedGlobalSectionsHomUnit`, and `…IntegralTransformQcoh.Basic` | Evaluation at 1 identifies Hom(O_X,M) with global sections as a base-linear equivalence, naturally in M; the scalar structures used for sections and tensor agree. |
| `ProjectiveLineEnd` | The preceding comparison and `…ProjTwistFunctor.Derived`, `…Cohomology.DerivedTwistSections`, `…TwistMonomialBasis` | On actual polynomial P¹ over every field, End(O(0) ⊕ O(1)) is isomorphic to the concrete Kronecker algebra; every right End module has projective dimension at most one. The isomorphism chooses a basis of Hom(O(0),O(1)). |
| `CoherentDerivedComparison` | `…DerivedCoherent.Modules`, `…SiblingFunctors.BoundedCoherent`, and derived-model comparison | For a Noetherian scheme, Dᵇ(Coh X) is equivalent to the bounded-coherent full subcategory of D_QCoh in the locally small model. Both functors preserve triangles and shifts. |
| `KroneckerBoundedDerived` | Production `Beilinson.KroneckerFinite`, `…DerivedCategory.SerreSubcategory`, and `KroneckerCompact` | The actual Dᵇ of finite-dimensional right Kronecker modules is equivalent to the compact ambient module derived category. Finite projective covers verify the Serre comparison; both directions preserve triangles and shifts. |
| `StacksCohomologyProbe` | `…ProjectiveSpaceHigherDirectImage.TwistAcyclicRange` | Negative twists in the Beilinson band have zero higher direct images in every degree, on the base-change model of projective space. |
| `StacksBeilinsonProbe` | `…ExampleGenerator.BeilinsonEquivalenceLinear` | The actual unbounded dg tensor functor is an exact equivalence; its dg algebra is concentrated in degree zero and its underlying ring is End(E). |
| `OrdinaryBeilinson` | The preceding theorem and the checked concentrated-dg adapters | At universe zero, convert the actual dg tensor functor to an exact equivalence from ordinary right End(E)-modules, with the cone sign corrected. |
| `BoundedBeilinson` | `OrdinaryBeilinson`, `ProjectivePerfectProbe`, and `CoherentDerivedComparison` | Over a field in Type 0, in every dimension including zero, the compact ordinary End(E)-module derived category is equivalent to actual Dᵇ(Coh Pⁿ). Both directions preserve triangles and shifts. |
| `ProjectiveLineWindow` | `ProjectiveLineEnd`, production `EndTransport`, and `…ExampleGenerator.QuasiCoherentGenerator` | End of the actual Fin 2 negative-window generator E = O ⊕ O(-1) is the concrete Kronecker algebra. Its comparison with the positive-window End uses chosen bases. |
| `ProjectiveLineBeilinson` | The preceding adapters and `KroneckerBoundedDerived` | For a field in Type 0, an actual exact equivalence Dᵇ(finite-dimensional right Kronecker modules) ≌ Dᵇ(Coh P¹), composed from the checked tensor functor and ring changes. |
| `PositiveWindow` | Production `EndTransport`, `SheafHomSections`, and the geometric twist functor | Over every commutative ring and in every dimension, E(n) is isomorphic to the actual positive twist sum. Twisting gives the corresponding End algebra isomorphism, without choosing Hom bases. |

| `CentralDegreeZero` | Central dg actions and the concentrated comparison | The ordinary right-module comparison preserves an additional central coefficient ring in both directions. |
| `OrdinaryBeilinsonLinear` | The actual ordinary tensor equivalence and central coefficients | The ordinary negative-window tensor functor is linear over the geometric coefficient ring, although its dg presentation is over ℤ. |

The Koszul import closure contains 92 Stacks modules, Koszul descent 228, the
ordinary-module comparison 53, the polynomial-matrix criterion 96, and the strict
dg adapter 456; the concentrated comparison uses a combined closure of 462. Counts
exclude mathlib and are for this revision.
Do not run `lake build Stacks` or import the umbrella module by default.

The unbounded geometric equivalence imports 8353 Stacks modules. The first build in
this environment took over two hours on four CPU cores, with a 16 GiB memory limit;
subsequent checks reuse the compiled artifacts. The production book remains independent.

The negative-twist higher-direct-image probe uses a base-change model of projective
space. It is not silently identified with polynomial Proj. The unbounded geometric
functor and the bounded adapters use the actual polynomial Proj throughout.

The geometric generator is E = O ⊕ O(-1) ⊕ … ⊕ O(-n). The object isomorphism E(n) ≅ T and the induced End algebra isomorphism are checked
by `PositiveWindow`. The remaining book-level boundaries are the comparison of the
positive-window tensor/Hom functor and, in general
dimension, replacing the compact source by Dᵇ of finite-dimensional ordinary modules.
The dimension-one bounded theorem uses a chosen Kronecker basis; it does not identify
the two arrows with particular coordinate sections.

Promotion to a production dependency requires keeping the exact declarations,
assumptions, model comparisons and build cost in the reuse ledger.

The geometric dg equivalence uses the cone triangulation; the original ordinary-module
comparison uses admissible-sequence triangles. The sign correction in
`DegreeZeroConeComparison` is required even though the underlying localizations
agree at equal universes.

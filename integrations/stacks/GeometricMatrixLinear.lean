module

public import Beilinson.BiproductEnd
public import GeometricMatrixEnd
public import PositiveWindow
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.TwistEndomorphisms

/-! Compatibility of the geometric matrix-to-End comparison with coefficient
scalars. This strengthens the ring comparison toward an algebra comparison. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ProjectiveGenerator
open Stacks.AlgebraicGeometry.TwistEndomorphisms

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Beilinson.GeometricMatrixLinear

universe u
variable (k : Type u) [Field k] (n : ℕ)

local instance baseLinear : Linear k (AlgebraicGeometry.Proj (polyGrading k n)).Modules :=
  Stacks.AlgebraicGeometry.Beilinson.projectiveSpaceModulesLinear k n

local instance matrixLinear : Linear k (_root_.SheafOfModules.{u}
    (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf (polyGrading k n))) :=
  Stacks.AlgebraicGeometry.Beilinson.projectiveSpaceModulesLinear k n

/-- Constant multiplication on a twist is the actual geometric scalar action. -/
theorem twistScalar_eq_smul (a : k) (d : ℤ) :
    twistScalar k n a d = a •
      𝟙 (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d) :=
  (twistScalar_eq_twistBaseScalar k n a d).trans (Category.comp_id _).symm

/-- The geometric matrix comparison sends constant diagonal matrices to scalar endomorphisms. -/
theorem matrix_scalar (a : k) :
    matrixRingEquivEnd k n (algebraMap k (endomorphismMatrices k n) a) =
      a • (1 : End (projTwistSum k n)) := by
  apply BiproductEnd.ext (twistFamily k n)
  intro j i
  rw [components_matrixRingEquivEnd, BiproductEnd.components_smul_one (twistFamily k n) k]
  by_cases hij : i = j
  · subst j
    rw [biproduct.ι_π_self]
    simpa only [twistScalar, twistFamily, matrixEntryHom, twistMulHom_apply, matrixEntry, Subalgebra.coe_algebraMap,
      Matrix.algebraMap_matrix_apply, ite_eq_left rfl, ite_true, MvPolynomial.algebraMap_eq, sub_self] using
        twistScalar_eq_smul k n a (-(i : ℤ))
  · rw [biproduct.ι_π_ne _ (Ne.symm hij), smul_zero]
    simp only [twistFamily, matrixEntryHom, twistMulHom_apply, matrixEntry, Subalgebra.coe_algebraMap,
      Matrix.algebraMap_matrix_apply, ite_eq_right hij]
    exact twistMul_zero (polyGrading k n) _ _ _ _

/-- The geometric matrix ring comparison respects the base field algebra structures. -/
def matrixAlgebraEquiv : endomorphismMatrices k n ≃ₐ[k] End (projTwistSum k n) :=
  { matrixRingEquivEnd k n with
    commutes' := fun a => by
      change matrixRingEquivEnd k n (algebraMap k (endomorphismMatrices k n) a) = a • 1
      exact matrix_scalar k n a }

/-- The compactness model is the actual negative-window End as a k-algebra. -/
def negativeAlgebraEquiv : StacksDraft.Perfect.beilinsonAlgebra k n ≃ₐ[k]
    End (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumModule k n) :=
  ((MatrixAlgebraComparison.algebraEquiv k n).trans (matrixAlgebraEquiv k n)).trans
    (EndTransport.iso k (GeometricMatrixEnd.generatorIso k n))

/-- The compactness model is the actual positive-window End as a k-algebra. -/
def positiveAlgebraEquiv : StacksDraft.Perfect.beilinsonAlgebra k n ≃ₐ[k]
    End (PositiveWindow.positiveGenerator k n) :=
  (negativeAlgebraEquiv k n).trans (PositiveWindow.endAlgebraEquiv k n)

#print axioms matrixAlgebraEquiv
#print axioms negativeAlgebraEquiv
#print axioms positiveAlgebraEquiv
#print axioms twistScalar_eq_smul
#print axioms matrix_scalar

end Beilinson.GeometricMatrixLinear

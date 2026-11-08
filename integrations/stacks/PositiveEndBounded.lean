module

public import GeometricMatrixLinear
public import FiniteScalarEquivalence
public import PositiveBounded

/-! An equivalence with the book's actual finite-dimensional right End(T)-module
source and actual D^b(Coh P^n) target. Its forward functor changes coefficients to
the matrix model, uses the negative-window tensor equivalence, and twists by O(n).
The remaining comparison with a separately defined classical RHom/tensor functor
is not part of this declaration. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.gradedAlgebra

namespace Beilinson.PositiveEndBounded

variable (k : Type) [Field k] (n : ℕ)

local instance baseLinear : Linear k (AlgebraicGeometry.Proj (polyGrading k n)).Modules :=
  Stacks.AlgebraicGeometry.Beilinson.projectiveSpaceModulesLinear k n

/-- The actual ordinary right End(T)-modules finite over the geometric base field. -/
abbrev finiteModules : ObjectProperty
    (ModuleCat.{0} (End (PositiveWindow.positiveGenerator k n))ᵐᵒᵖ) :=
  FiniteModuleCategory.finiteModules k (End (PositiveWindow.positiveGenerator k n))ᵐᵒᵖ

/-- Identify the actual finite right-module derived source with the matrix presentation. -/
def matrixSourceEquivalence :=
  (FiniteScalarEquivalence.boundedEquivalence
    (AlgEquiv.op (GeometricMatrixLinear.positiveAlgebraEquiv k n))).symm

instance matrixSourceEquivalence_commShift : (matrixSourceEquivalence k n).functor.CommShift ℤ :=
  inferInstanceAs ((FiniteScalarEquivalence.boundedEquivalence
    (AlgEquiv.op (GeometricMatrixLinear.positiveAlgebraEquiv k n))).inverse.CommShift ℤ)

instance matrixSourceEquivalence_isTriangulated : (matrixSourceEquivalence k n).functor.IsTriangulated :=
  inferInstanceAs ((FiniteScalarEquivalence.boundedEquivalence
    (AlgEquiv.op (GeometricMatrixLinear.positiveAlgebraEquiv k n))).inverse.IsTriangulated)

/-- The bounded Beilinson equivalence with exactly the positive-window End(T) source. -/
def equivalence : DerivedCategory.Bounded (finiteModules k n).FullSubcategory ≌
    DerivedCategory.Bounded (AlgebraicGeometry.SheafOfModules.CoherentModules
      (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf) :=
  (matrixSourceEquivalence k n).trans (PositiveBounded.equivalence k n)

instance equivalence_commShift : (equivalence k n).functor.CommShift ℤ := by
  change ((matrixSourceEquivalence k n).functor ⋙
    (PositiveBounded.equivalence k n).functor).CommShift ℤ
  infer_instance

instance equivalence_isTriangulated : (equivalence k n).functor.IsTriangulated := by
  change ((matrixSourceEquivalence k n).functor ⋙
    (PositiveBounded.equivalence k n).functor).IsTriangulated
  infer_instance

instance equivalence_inverseCommShift : (equivalence k n).inverse.CommShift ℤ :=
  (equivalence k n).commShiftInverse ℤ

instance equivalence_inverseIsTriangulated : (equivalence k n).inverse.IsTriangulated := by
  let E := equivalence k n
  let : E.toAdjunction.CommShift ℤ := E.toAdjunction.commShift_of_leftAdjoint ℤ
  exact E.toAdjunction.isTriangulated_rightAdjoint

#print axioms equivalence
#print axioms equivalence_isTriangulated
#print axioms equivalence_inverseIsTriangulated

end Beilinson.PositiveEndBounded

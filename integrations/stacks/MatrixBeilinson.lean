module

public import GeometricMatrixEnd
public import FiniteBoundedDerived
public import BoundedBeilinson

/-! An end-to-end bounded Beilinson equivalence in every dimension.
The source is the actual bounded derived category of finite-dimensional modules
over the polynomial-matrix Beilinson algebra; the target is the actual D^b(Coh P^n).
The geometric algebra identification uses the negative-window generator. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ExampleGenerator (twistSumModule)
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isClosedUnderIsomorphisms_isCompactObject isTriangulated_isCompactObject

namespace Beilinson.MatrixBeilinson

variable (k : Type) [Field k] (n : ℕ)

local instance finiteAlgebra : Module.Finite k (StacksDraft.Perfect.beilinsonAlgebra k n) :=
  MatrixAlgebraComparison.finite_algebra k n

/-- The cohomological compactness criterion in the actual finite-module Serre presentation. -/
theorem algebra_bounded_iff_compact
    (K : DerivedCategory (ModuleCat.{0} (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ)) :
    DerivedCategoryB.derivedCategoryBBounded
      (FiniteModuleCategory.finiteModules k (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ) K ↔
        IsCompactObject.{0} K :=
  (FiniteBoundedDerived.bounded_iff_finite_total k
    (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ K).trans
      (StacksDraft.Perfect.hasFiniteTotalCohomology_iff_isCompactObject k n K)

/-- D^b of finite-dimensional matrix-algebra modules is the compact derived category. -/
def algebraCompactEquivalence :=
  FiniteBoundedDerived.compactEquivalence k (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ
    (algebra_bounded_iff_compact k n)

instance algebraCompactEquivalence_commShift :
    (algebraCompactEquivalence k n).functor.CommShift ℤ :=
  inferInstanceAs ((FiniteBoundedDerived.compactEquivalence k
    (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ (algebra_bounded_iff_compact k n)).functor.CommShift ℤ)

instance algebraCompactEquivalence_isTriangulated :
    (algebraCompactEquivalence k n).functor.IsTriangulated :=
  inferInstanceAs ((FiniteBoundedDerived.compactEquivalence k
    (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ (algebra_bounded_iff_compact k n)).functor.IsTriangulated)

/-- Change scalars from the polynomial-matrix algebra to the actual ordinary End(E) ring. -/
abbrev changeRing : ModuleCat.{0} (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ ⥤
    ModuleCat.{0} (End (twistSumModule k n))ᵐᵒᵖ :=
  ModuleCat.restrictScalars (RingEquiv.op (GeometricMatrixEnd.ringEquiv k n)).symm.toRingHom

instance changeRing_isEquivalence : (changeRing k n).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv _

def derivedChangeRing : DerivedCategory (ModuleCat.{0} (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ) ⥤
    OrdinaryBeilinson.endDerivedCategory k n := (changeRing k n).mapDerivedCategory

instance derivedChangeRing_isEquivalence : (derivedChangeRing k n).IsEquivalence :=
  Stacks.Injectives.mapDerivedCategory_isEquivalence (changeRing k n)

instance derivedChangeRing_commShift : (derivedChangeRing k n).CommShift ℤ :=
  inferInstanceAs ((changeRing k n).mapDerivedCategory.CommShift ℤ)

instance derivedChangeRing_isTriangulated : (derivedChangeRing k n).IsTriangulated :=
  inferInstanceAs ((changeRing k n).mapDerivedCategory.IsTriangulated)

def derivedEquivalence := (derivedChangeRing k n).asEquivalence

instance derivedEquivalence_commShift : (derivedEquivalence k n).functor.CommShift ℤ :=
  inferInstanceAs ((derivedChangeRing k n).CommShift ℤ)

instance derivedEquivalence_isTriangulated : (derivedEquivalence k n).functor.IsTriangulated :=
  inferInstanceAs ((derivedChangeRing k n).IsTriangulated)

/-- The ring change preserves and reflects compact objects. -/
def compactTransport :
    ObjectProperty.FullSubcategory (IsCompactObject.{0}
      (C := DerivedCategory (ModuleCat.{0} (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ))) ≌
    ObjectProperty.FullSubcategory (IsCompactObject.{0}
      (C := OrdinaryBeilinson.endDerivedCategory k n)) :=
  (derivedEquivalence k n).congrFullSubcategory (by
    funext K
    exact propext (isCompactObject_iff_isCompactObject_obj (derivedChangeRing k n) K).symm)

instance compactTransport_commShift : (compactTransport k n).functor.CommShift ℤ := by
  dsimp only [compactTransport, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

instance compactTransport_isTriangulated : (compactTransport k n).functor.IsTriangulated := by
  dsimp only [compactTransport, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

/-- The bounded projective-space equivalence, composed from the actual checked functors. -/
def equivalence :
    DerivedCategory.Bounded (FiniteModuleCategory.finiteModules k (StacksDraft.Perfect.beilinsonAlgebra k n)ᵐᵒᵖ).FullSubcategory ≌
      DerivedCategory.Bounded (SheafOfModules.CoherentModules
        (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf) :=
  (algebraCompactEquivalence k n).trans
    ((compactTransport k n).trans (BoundedBeilinson.coherentEquivalence k n))

instance equivalence_commShift : (equivalence k n).functor.CommShift ℤ := by
  change ((algebraCompactEquivalence k n).functor ⋙
    (compactTransport k n).functor ⋙ (BoundedBeilinson.coherentEquivalence k n).functor).CommShift ℤ
  infer_instance

instance equivalence_isTriangulated : (equivalence k n).functor.IsTriangulated := by
  change ((algebraCompactEquivalence k n).functor ⋙
    (compactTransport k n).functor ⋙ (BoundedBeilinson.coherentEquivalence k n).functor).IsTriangulated
  infer_instance

instance equivalence_inverseCommShift : (equivalence k n).inverse.CommShift ℤ :=
  (equivalence k n).commShiftInverse ℤ

instance equivalence_inverseIsTriangulated : (equivalence k n).inverse.IsTriangulated := by
  let E := equivalence k n
  let : E.toAdjunction.CommShift ℤ := E.toAdjunction.commShift_of_leftAdjoint ℤ
  exact E.toAdjunction.isTriangulated_rightAdjoint

#print axioms Beilinson.MatrixBeilinson.equivalence
#print axioms Beilinson.MatrixBeilinson.equivalence_isTriangulated
#print axioms Beilinson.MatrixBeilinson.equivalence_inverseIsTriangulated

end Beilinson.MatrixBeilinson

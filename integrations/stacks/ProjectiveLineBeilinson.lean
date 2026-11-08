module

public import ProjectiveLineWindow
public import KroneckerBoundedDerived
public import BoundedBeilinson

/-! An end-to-end bounded Beilinson equivalence on the projective line.
The source is the actual bounded derived category of finite-dimensional modules
over the concrete Kronecker algebra; the target is the actual D^b(Coh P^1).
The chosen algebra identification uses the negative-window generator. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ExampleGenerator (twistSumModule)
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isClosedUnderIsomorphisms_isCompactObject isTriangulated_isCompactObject

namespace Beilinson.ProjectiveLineBeilinson

variable (k : Type) [Field k]

/-- Change scalars from Kronecker to the actual ordinary End(E) ring. -/
abbrev changeRing : ModuleCat.{0} (Kronecker.Algebra k)ᵐᵒᵖ ⥤
    ModuleCat.{0} (End (twistSumModule k 1))ᵐᵒᵖ :=
  ModuleCat.restrictScalars (RingEquiv.op (ProjectiveLineWindow.ringEquiv k)).symm.toRingHom

instance changeRing_isEquivalence : (changeRing k).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv _

def derivedChangeRing : DerivedCategory (ModuleCat.{0} (Kronecker.Algebra k)ᵐᵒᵖ) ⥤
    OrdinaryBeilinson.endDerivedCategory k 1 := (changeRing k).mapDerivedCategory

instance derivedChangeRing_isEquivalence : (derivedChangeRing k).IsEquivalence :=
  Stacks.Injectives.mapDerivedCategory_isEquivalence (changeRing k)

instance derivedChangeRing_commShift : (derivedChangeRing k).CommShift ℤ :=
  inferInstanceAs ((changeRing k).mapDerivedCategory.CommShift ℤ)

instance derivedChangeRing_isTriangulated : (derivedChangeRing k).IsTriangulated :=
  inferInstanceAs ((changeRing k).mapDerivedCategory.IsTriangulated)

def derivedEquivalence := (derivedChangeRing k).asEquivalence

instance derivedEquivalence_commShift : (derivedEquivalence k).functor.CommShift ℤ :=
  inferInstanceAs ((derivedChangeRing k).CommShift ℤ)

instance derivedEquivalence_isTriangulated : (derivedEquivalence k).functor.IsTriangulated :=
  inferInstanceAs ((derivedChangeRing k).IsTriangulated)

/-- The ring change preserves and reflects compact objects. -/
def compactTransport :
    ObjectProperty.FullSubcategory (IsCompactObject.{0}
      (C := DerivedCategory (ModuleCat.{0} (Kronecker.Algebra k)ᵐᵒᵖ))) ≌
    ObjectProperty.FullSubcategory (IsCompactObject.{0}
      (C := OrdinaryBeilinson.endDerivedCategory k 1)) :=
  (derivedEquivalence k).congrFullSubcategory (by
    funext K
    exact propext (isCompactObject_iff_isCompactObject_obj (derivedChangeRing k) K).symm)

instance compactTransport_commShift : (compactTransport k).functor.CommShift ℤ := by
  dsimp only [compactTransport, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

instance compactTransport_isTriangulated : (compactTransport k).functor.IsTriangulated := by
  dsimp only [compactTransport, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

/-- The bounded projective-line equivalence, composed from the actual checked functors. -/
def equivalence :
    DerivedCategory.Bounded (Kronecker.finiteRightModules.{0,0} (k := k)).FullSubcategory ≌
      DerivedCategory.Bounded (SheafOfModules.CoherentModules
        (AlgebraicGeometry.Proj (polyGrading k 1)).ringCatSheaf) :=
  (KroneckerBoundedDerived.compactEquivalence k).trans
    ((compactTransport k).trans (BoundedBeilinson.coherentEquivalence k 1))

instance equivalence_commShift : (equivalence k).functor.CommShift ℤ := by
  change ((KroneckerBoundedDerived.compactEquivalence k).functor ⋙
    (compactTransport k).functor ⋙ (BoundedBeilinson.coherentEquivalence k 1).functor).CommShift ℤ
  infer_instance

instance equivalence_isTriangulated : (equivalence k).functor.IsTriangulated := by
  change ((KroneckerBoundedDerived.compactEquivalence k).functor ⋙
    (compactTransport k).functor ⋙ (BoundedBeilinson.coherentEquivalence k 1).functor).IsTriangulated
  infer_instance

instance equivalence_inverseCommShift : (equivalence k).inverse.CommShift ℤ :=
  (equivalence k).commShiftInverse ℤ

instance equivalence_inverseIsTriangulated : (equivalence k).inverse.IsTriangulated := by
  let E := equivalence k
  let : E.toAdjunction.CommShift ℤ := E.toAdjunction.commShift_of_leftAdjoint ℤ
  exact E.toAdjunction.isTriangulated_rightAdjoint

#print axioms Beilinson.ProjectiveLineBeilinson.equivalence
#print axioms Beilinson.ProjectiveLineBeilinson.equivalence_isTriangulated
#print axioms Beilinson.ProjectiveLineBeilinson.equivalence_inverseIsTriangulated

end Beilinson.ProjectiveLineBeilinson

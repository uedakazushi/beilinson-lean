module

public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-! Cancellation of successive coefficient changes on actual ordinary derived categories. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

namespace Beilinson.RingChangeDerived

universe u
variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- Undo a ring isomorphism before restricting along its composite with another one. -/
def cancelOpposite (f : R ≃+* S) (e : S ≃+* T) :
    ModuleCat.restrictScalars.{u} (RingEquiv.op e.symm).toRingHom ⋙
      ModuleCat.restrictScalars (RingEquiv.op (f.trans e)).toRingHom ≅
    ModuleCat.restrictScalars (RingEquiv.op f).toRingHom :=
  (ModuleCat.restrictScalarsComp' (RingEquiv.op (f.trans e)).toRingHom
    (RingEquiv.op e.symm).toRingHom (RingEquiv.op f).toRingHom (by
      ext a
      simp)).symm

/-- The same cancellation holds for the actual derived coefficient-change functors. -/
def cancelOppositeDerived (f : R ≃+* S) (e : S ≃+* T) :
    (ModuleCat.restrictScalars.{u} (RingEquiv.op e.symm).toRingHom).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars (RingEquiv.op (f.trans e)).toRingHom).mapDerivedCategory ≅
    (ModuleCat.restrictScalars (RingEquiv.op f).toRingHom).mapDerivedCategory :=
  Dualizing.mapDerivedCategoryCompNatIso _ _ _ (cancelOpposite f e)

#print axioms cancelOppositeDerived

/-- Change the target coefficient ring of a derived-valued functor. -/
def postcompose {C : Type*} [Category* C] (e : S ≃+* T)
    (P : C ⥤ DerivedCategory (ModuleCat.{u} Sᵐᵒᵖ)) :
    C ⥤ DerivedCategory (ModuleCat.{u} Tᵐᵒᵖ) :=
  P ⋙ (ModuleCat.restrictScalars (RingEquiv.op e.symm).toRingHom).mapDerivedCategory

/-- Package coefficient cancellation before specializing the source to a large geometric model. -/
def liftComparison {C : Type*} [Category* C] (f : R ≃+* S) (e : S ≃+* T)
    (P : C ⥤ DerivedCategory (ModuleCat.{u} Sᵐᵒᵖ))
    (G : C ⥤ DerivedCategory (ModuleCat.{u} Rᵐᵒᵖ))
    (α : G ≅ P ⋙ (ModuleCat.restrictScalars (RingEquiv.op f).toRingHom).mapDerivedCategory) :
    G ≅ (P ⋙ (ModuleCat.restrictScalars (RingEquiv.op e.symm).toRingHom).mapDerivedCategory) ⋙
      (ModuleCat.restrictScalars (RingEquiv.op (f.trans e)).toRingHom).mapDerivedCategory :=
  α ≪≫ Functor.isoWhiskerLeft P (cancelOppositeDerived f e).symm ≪≫
    (Functor.associator _ _ _).symm

end Beilinson.RingChangeDerived

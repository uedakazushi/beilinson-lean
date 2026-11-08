module

public import RingChangeDerived

/-! Derive the explicit coefficient-ring equivalence before specializing to geometric End rings. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

namespace Beilinson.DerivedRingEquivalence

universe u
variable {R S : Type u} [Ring R] [Ring S]

/-- The ordinary right-module equivalence induced by a ring isomorphism, derived explicitly. -/
def equivalence (e : R ≃+* S) :
    DerivedCategory (ModuleCat.{u} Sᵐᵒᵖ) ≌ DerivedCategory (ModuleCat.{u} Rᵐᵒᵖ) := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.op e)
  letI : E.functor.Additive := inferInstanceAs
    (ModuleCat.restrictScalars (RingEquiv.op e).toRingHom).Additive
  letI : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  exact Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E

#print axioms equivalence

/-- Whisker the coefficient comparison while all category and ring data are still abstract. -/
def whiskerComparison {T : Type u} [Ring T] {C D : Type*} [Category* C] [Category* D]
    (f : R ≃+* S) (e : S ≃+* T) (J : D ⥤ C)
    (P : C ⥤ DerivedCategory (ModuleCat.{u} Sᵐᵒᵖ))
    (G : C ⥤ DerivedCategory (ModuleCat.{u} Rᵐᵒᵖ))
    (α : G ≅ P ⋙ (ModuleCat.restrictScalars (RingEquiv.op f).toRingHom).mapDerivedCategory) :
    J ⋙ G ≅ (J ⋙ RingChangeDerived.postcompose e P) ⋙
      (ModuleCat.restrictScalars (RingEquiv.op (f.trans e)).toRingHom).mapDerivedCategory :=
  Functor.isoWhiskerLeft J (RingChangeDerived.liftComparison f e P G α) ≪≫
    (Functor.associator _ _ _).symm

end Beilinson.DerivedRingEquivalence

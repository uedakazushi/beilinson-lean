module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! Total right derived functors commute with an explicitly identified change of localization model. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory

namespace Beilinson.DerivedFunctorModels

universe u v u₁ v₁ u₂ v₂ uH vH
variable {C : Type u} [Category.{v} C]
variable {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]
variable {H : Type uH} [Category.{vH} H]
variable (W : MorphismProperty C) (F : C ⥤ H) [F.HasRightDerivedFunctor W]
variable (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂) [L₁.IsLocalization W] [L₂.IsLocalization W]
variable (E : D₁ ≌ D₂) (sq : L₁ ⋙ E.functor ≅ L₂)

/-- Compare the right derived functors computed in two chosen localization models. -/
def rightDerivedIso : F.totalRightDerived L₁ W ≅ E.functor ⋙ F.totalRightDerived L₂ W := by
  let Φ := LocalizerMorphism.id W
  let iso : Φ.functor ⋙ L₂ ≅ L₁ ⋙ E.functor := sq.symm
  let α₂ := F.totalRightDerivedUnit L₂ W
  let α : F ⟶ L₁ ⋙ (E.functor ⋙ F.totalRightDerived L₂ W) :=
    (Iso.refl F).inv ≫ Functor.whiskerLeft Φ.functor α₂ ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight iso.hom _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft L₁ (Iso.refl _).hom
  have : (E.functor ⋙ F.totalRightDerived L₂ W).IsRightDerivedFunctor α W :=
    (Φ.isRightDerivedFunctor_iff_precomp L₁ L₂ E.functor iso α α₂
      (Iso.refl _) (Iso.refl _) rfl).1 inferInstance
  exact Functor.rightDerivedNatIso _ _ (F.totalRightDerivedUnit L₁ W) α W (Iso.refl F)

#print axioms rightDerivedIso

end Beilinson.DerivedFunctorModels

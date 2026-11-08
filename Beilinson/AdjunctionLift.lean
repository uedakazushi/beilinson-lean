module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Restrict the target of an adjunction when the left adjoint lands in a full subcategory. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory

namespace Beilinson.AdjunctionLift

universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (P : ObjectProperty D) {F : C ⥤ D} {G : D ⥤ C}

/-- The restricted right adjoint is the original right adjoint after inclusion. -/
def restrictTarget (adj : F ⊣ G) (hF : ∀ X, P (F.obj X)) :
    P.lift F hF ⊣ P.ι ⋙ G :=
  adj.restrictFullyFaithful (Functor.FullyFaithful.id C) P.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- Identify a chosen equivalence inverse with a specified right adjoint. -/
def inverseIso (e : C ≌ D) (G : D ⥤ C) (adj : e.functor ⊣ G) : e.inverse ≅ G :=
  Adjunction.rightAdjointUniq e.toAdjunction adj

/-- Cancel a coefficient equivalence on the right of a functor comparison. -/
def cancelRight {A : Type*} [Category* A] (e : C ≌ D)
    (F : A ⥤ D) (Q : A ⥤ C) (α : F ≅ Q ⋙ e.functor) : F ⋙ e.inverse ≅ Q :=
  Functor.isoWhiskerRight α _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _

end Beilinson.AdjunctionLift

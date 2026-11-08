module

public import Mathlib.CategoryTheory.Equivalence

/-! Move a commuting square of equivalences to the inverse functors. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory

namespace Beilinson.EquivalenceSquare

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
variable (e : C ≌ D) (f : C' ≌ D') (i : C ⥤ C') (j : D ⥤ D')
variable (α : e.functor ⋙ j ≅ i ⋙ f.functor)

/-- Cancel the upper equivalence after substituting the given commuting square. -/
def cancel : (e.inverse ⋙ i) ⋙ f.functor ≅ j :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ α.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.counitIso _ ≪≫
    Functor.leftUnitor _

/-- A commuting square for the forward equivalences also commutes for their inverses. -/
def inverse : e.inverse ⋙ i ≅ j ⋙ f.inverse :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ f.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (cancel e f i j α) _

end Beilinson.EquivalenceSquare

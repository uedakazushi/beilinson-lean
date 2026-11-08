module

public import Beilinson.EndTransport

/-! Component formulas for finite biproduct endomorphisms, kept abstract so the
geometric applications do not unfold their concrete endomorphism rings. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Beilinson.BiproductEnd

universe u v w z
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {J : Type z} (F : J → C) [HasBiproduct F]

/-- Endomorphisms of a biproduct are determined by their matrix components. -/
theorem ext (a b : End (⨁ F))
    (h : ∀ j i, biproduct.ι F j ≫ a.asHom ≫ biproduct.π F i =
      biproduct.ι F j ≫ b.asHom ≫ biproduct.π F i) : a = b := by
  apply End.ext
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro i
  simpa only [Category.assoc] using h j i

/-- Matrix components of a scalar endomorphism retain the original Hom module structure. -/
theorem components_smul_one (k : Type u) [CommSemiring k] [Linear k C]
    (a : k) (j i : J) :
    biproduct.ι F j ≫ (a • (1 : End (⨁ F))).asHom ≫ biproduct.π F i =
      a • (biproduct.ι F j ≫ biproduct.π F i) := by
  simp only [End.smul_asHom, End.one_asHom, Linear.comp_smul, Linear.smul_comp,
    Category.id_comp]

end Beilinson.BiproductEnd

module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Hom transport over a specified endomorphism-ring isomorphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory

namespace Beilinson.EndRingYoneda

universe u v u'
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v} D] [Preadditive D]
variable (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
variable (X : C) {Y : D} (e : F.obj X ≅ Y) (φ : End X ≃+* End Y)
variable (hφ : ∀ a, (φ a).asHom = e.inv ≫ F.map a.asHom ≫ e.hom)

def source : C ⥤ ModuleCat.{v} (End Y)ᵐᵒᵖ :=
  preadditiveCoyonedaObj X ⋙ ModuleCat.restrictScalars (RingEquiv.op φ.symm).toRingHom

def homLinearMap (Z : C) : (source X φ).obj Z →ₗ[(End Y)ᵐᵒᵖ]
    (preadditiveCoyonedaObj Y).obj (F.obj Z) where
  toFun h := e.inv ≫ F.map h
  map_add' h g := by
    change e.inv ≫ F.map (h + g) = _
    rw [F.map_add, Preadditive.comp_add]
  map_smul' a h := by
    change e.inv ≫ F.map ((φ.symm a.unop).asHom ≫ h) =
      a.unop.asHom ≫ (e.inv ≫ F.map h)
    have ha := hφ (φ.symm a.unop)
    rw [RingEquiv.apply_symm_apply] at ha
    rw [ha, F.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

def homLinearEquiv (Z : C) : (source X φ).obj Z ≃ₗ[(End Y)ᵐᵒᵖ]
    (preadditiveCoyonedaObj Y).obj (F.obj Z) :=
  LinearEquiv.ofBijective (homLinearMap F X e φ hφ Z) (by
    constructor
    · intro h g hh
      apply F.map_injective
      have h' := congrArg (fun f => e.hom ≫ f) hh
      simpa only [homLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
        Iso.hom_inv_id_assoc] using h'
    · intro h
      obtain ⟨g, hg⟩ := F.map_surjective (e.hom ≫ h)
      refine ⟨g, ?_⟩
      change e.inv ≫ F.map g = h
      rw [hg, Iso.inv_hom_id_assoc])

/-- The given ring identification gives a natural comparison on actual right modules. -/
def functorIso : source X φ ≅ F ⋙ preadditiveCoyonedaObj Y :=
  NatIso.ofComponents (fun Z => (homLinearEquiv F X e φ hφ Z).toModuleIso) (by
    intro Z W g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change e.inv ≫ F.map (h ≫ g) = (e.inv ≫ F.map h) ≫ F.map g
    simp only [F.map_comp, Category.assoc])

end Beilinson.EndRingYoneda

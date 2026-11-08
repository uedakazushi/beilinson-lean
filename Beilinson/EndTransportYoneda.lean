module

public import Mathlib.Algebra.Homology.Additive
public import Beilinson.EndTransport
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Naturality of the right End action under a fully faithful linear functor
and an isomorphism of the chosen generator. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory

namespace Beilinson.EndTransportYoneda

universe u v w w'
variable (k : Type u) [CommSemiring k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type w'} [Category.{v} D] [Preadditive D] [Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
variable (X : C) {Y : D} (e : F.obj X ≅ Y)

/-- The endomorphism algebra map induced by the functor and generator isomorphism. -/
def algebraEquiv : End X ≃ₐ[k] End Y :=
  (EndTransport.mapEquiv k F X).trans (EndTransport.iso k e)

/-- Hom from the new generator, restricted to the old right endomorphism ring. -/
def transportedHom : C ⥤ ModuleCat.{v} (End X)ᵐᵒᵖ :=
  F ⋙ preadditiveCoyonedaObj Y ⋙
    ModuleCat.restrictScalars (RingEquiv.op (algebraEquiv k F X e).toRingEquiv).toRingHom

instance transportedHom_additive : (transportedHom k F X e).Additive :=
  inferInstanceAs ((F ⋙ preadditiveCoyonedaObj Y ⋙
    ModuleCat.restrictScalars (RingEquiv.op (algebraEquiv k F X e).toRingEquiv).toRingHom).Additive)

/-- The comparison on Hom spaces intertwines precomposition, hence the right End action. -/
def homLinearMap (Z : C) :
    (preadditiveCoyonedaObj X).obj Z →ₗ[(End X)ᵐᵒᵖ] (transportedHom k F X e).obj Z where
  toFun h := e.inv ≫ F.map h
  map_add' h g := by
    change e.inv ≫ F.map ((h : X ⟶ Z) + g) =
      e.inv ≫ F.map h + e.inv ≫ F.map g
    rw [F.map_add, Preadditive.comp_add]
  map_smul' a h := by
    change e.inv ≫ F.map (a.unop.asHom ≫ h) =
      ((algebraEquiv k F X e) a.unop).asHom ≫ (e.inv ≫ F.map h)
    change _ = (e.inv ≫ F.map a.unop.asHom ≫ e.hom) ≫ (e.inv ≫ F.map h)
    simp only [F.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- Full faithfulness makes the comparison an isomorphism of actual right modules. -/
def homLinearEquiv (Z : C) :
    (preadditiveCoyonedaObj X).obj Z ≃ₗ[(End X)ᵐᵒᵖ] (transportedHom k F X e).obj Z :=
  LinearEquiv.ofBijective (homLinearMap k F X e Z) (by
    constructor
    · intro h g hh
      apply F.map_injective
      have := congrArg (fun f => e.hom ≫ f) hh
      simpa only [homLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
        Iso.hom_inv_id_assoc] using this
    · intro h
      obtain ⟨g, hg⟩ := F.map_surjective (e.hom ≫ h)
      refine ⟨g, ?_⟩
      change e.inv ≫ F.map g = h
      rw [hg, Iso.inv_hom_id_assoc])

/-- The right-module comparison is natural in the target object of Hom. -/
def homFunctorIso : preadditiveCoyonedaObj X ≅ transportedHom k F X e :=
  NatIso.ofComponents (fun Z => (homLinearEquiv k F X e Z).toModuleIso) (by
    intro Z W g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change e.inv ≫ F.map (h ≫ g) = (e.inv ≫ F.map h) ≫ F.map g
    simp only [F.map_comp, Category.assoc])

/-- The same natural comparison acts on complexes, including their differentials. -/
def homComplexFunctorIso {ι : Type*} (c : ComplexShape ι) :
    (preadditiveCoyonedaObj X).mapHomologicalComplex c ≅
      (transportedHom k F X e).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (homFunctorIso k F X e) c

end Beilinson.EndTransportYoneda

module

public import Beilinson.KroneckerFinite
public import KroneckerCompact
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.Modules
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! The actual bounded derived category of finite-dimensional Kronecker modules.
The finite projective covers proved in the production library verify the Serre
subcategory comparison, rather than assuming a comparison of derived categories. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] isClosedUnderIsomorphisms_isCompactObject isTriangulated_isCompactObject

namespace Beilinson.KroneckerBoundedDerived

universe u
variable (k : Type u) [Field k]

abbrev finiteModules : ObjectProperty (ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ) :=
  Kronecker.finiteRightModules

local instance finiteLimits : PreservesFiniteLimits (finiteModules k).ι :=
  (finiteModules k).preservesFiniteLimits_ι
local instance finiteColimits : PreservesFiniteColimits (finiteModules k).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass (finiteModules k)

private theorem covers {X Y : ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ}
    (f : X ⟶ Y) (hf : Epi f) (hY : finiteModules k Y) :
    ∃ (P : ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ) (g : P ⟶ X),
      finiteModules k P ∧ Epi (g ≫ f) := by
  let := hf
  exact Kronecker.finiteRightModules_coversEpis k f hY

private instance full_minus :
    (DerivedCategory.Minus.ι ⋙ (finiteModules k).ι.mapDerivedCategory).Full :=
  (ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory (finiteModules k) (fun {_ _} f hf hY => covers k f hf hY)).1

private instance faithful_minus :
    (DerivedCategory.Minus.ι ⋙ (finiteModules k).ι.mapDerivedCategory).Faithful :=
  (ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory (finiteModules k) (fun {_ _} f hf hY => covers k f hf hY)).2.1

private theorem bounded_le_minus :
    (DerivedCategory.TStructure.t (C := (finiteModules k).FullSubcategory)).bounded ≤
      (DerivedCategory.TStructure.t (C := (finiteModules k).FullSubcategory)).minus :=
  fun _ h => h.2

private instance full_bounded :
    (DerivedCategory.Bounded.ι ⋙ (finiteModules k).ι.mapDerivedCategory).Full :=
  inferInstanceAs (ObjectProperty.ιOfLE (bounded_le_minus k) ⋙
    (DerivedCategory.Minus.ι ⋙ (finiteModules k).ι.mapDerivedCategory)).Full

private instance faithful_bounded :
    (DerivedCategory.Bounded.ι ⋙ (finiteModules k).ι.mapDerivedCategory).Faithful :=
  inferInstanceAs (ObjectProperty.ιOfLE (bounded_le_minus k) ⋙
    (DerivedCategory.Minus.ι ⋙ (finiteModules k).ι.mapDerivedCategory)).Faithful

local instance boundedClosed :
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k)).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryBBounded_isClosedUnderIsomorphisms _
    (WeakSerre.isWeakSerre_of_isWeakSerreClass (finiteModules k))

/-- The canonical derived inclusion, restricted to bounded finite-dimensional cohomology. -/
def comparison : DerivedCategory.Bounded (finiteModules k).FullSubcategory ⥤
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryBBounded (finiteModules k)).lift
    (DerivedCategory.Bounded.ι ⋙ (finiteModules k).ι.mapDerivedCategory) fun K =>
      ⟨⟨(DerivedCategoryB.isBoundedBelow_mapDerivedCategory_obj_iff _ K.obj).2
          ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K.obj).2 K.property.1),
        (DerivedCategoryB.isBoundedAbove_mapDerivedCategory_obj_iff _ K.obj).2
          ((DerivedCategoryB.isBoundedAbove_iff_exists_isLE K.obj).2 K.property.2)⟩,
        fun i => (finiteModules k).prop_of_iso
          (((finiteModules k).ι.mapDerivedCategoryHomologyIso i).app K.obj).symm
          ((DerivedCategory.homologyFunctor _ i).obj K.obj).property⟩

instance comparison_full : (comparison k).Full where
  map_surjective f := by
    obtain ⟨g, hg⟩ := (DerivedCategory.Bounded.ι ⋙
      (finiteModules k).ι.mapDerivedCategory).map_surjective f.hom
    exact ⟨g, ObjectProperty.hom_ext _ hg⟩

instance comparison_faithful : (comparison k).Faithful where
  map_injective h := (DerivedCategory.Bounded.ι ⋙
    (finiteModules k).ι.mapDerivedCategory).map_injective (congrArg (fun q => q.hom) h)

instance comparison_essSurj : (comparison k).EssSurj where
  mem_essImage K := by
    have hK := (ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory
      (finiteModules k) (fun {_ _} f hf hY => covers k f hf hY)).2.2 K.obj
    obtain ⟨Y, ⟨e⟩⟩ := hK.mpr
      ⟨(DerivedCategoryB.isBoundedAbove_iff_exists_isLE _).mp K.property.1.2, K.property.2⟩
    have hb : DerivedCategoryB.IsBoundedBelow Y.obj :=
      (DerivedCategoryB.isBoundedBelow_mapDerivedCategory_obj_iff _ Y.obj).mp
        (DerivedCategoryB.isBoundedBelow_of_iso e.symm K.property.1.1)
    exact ⟨⟨Y.obj, (DerivedCategoryB.isBoundedBelow_iff_exists_isGE Y.obj).mp hb, Y.property⟩,
      ⟨ObjectProperty.isoMk _ e⟩⟩

instance comparison_isEquivalence : (comparison k).IsEquivalence := {}

def equivalence : DerivedCategory.Bounded (finiteModules k).FullSubcategory ≌
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k)).FullSubcategory :=
  (comparison k).asEquivalence

/-- Forgetting the cohomology condition gives the ordinary derived inclusion. -/
def comparisonCompInclusionIso : comparison k ⋙
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k)).ι ≅
      DerivedCategory.Bounded.ι ⋙ (finiteModules k).ι.mapDerivedCategory := Iso.refl _

instance comparison_commShift : (comparison k).CommShift ℤ :=
  Functor.CommShift.ofComp (comparisonCompInclusionIso k) ℤ

instance comparisonCompInclusionIso_commShift :
    NatTrans.CommShift (comparisonCompInclusionIso k).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance comparison_isTriangulated : (comparison k).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (comparisonCompInclusionIso k)).2 inferInstance

/-- The Serre-subcategory condition is exactly the checked compactness condition. -/
theorem bounded_iff_compact (K : DerivedCategory (ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ)) :
    DerivedCategoryB.derivedCategoryBBounded (finiteModules k) K ↔ IsCompactObject.{u} K :=
  (and_congr (and_congr
    (DerivedCategoryB.isBoundedBelow_iff_exists_isGE K)
    (DerivedCategoryB.isBoundedAbove_iff_exists_isLE K)) Iff.rfl).trans
      (KroneckerCompact.compact_iff_bounded_finite_cohomology (k := k) K).symm

/-- Repackage the checked cohomology criterion as an equivalence of subcategories. -/
def cohomologyCompactEquivalence :
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k)).FullSubcategory ≌
      ObjectProperty.FullSubcategory (IsCompactObject.{u}
        (C := DerivedCategory (ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ))) :=
  (CategoryTheory.Equivalence.refl
    (C := DerivedCategory (ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ))).congrFullSubcategory (by
    funext K
    exact propext (bounded_iff_compact k K).symm)

instance cohomologyCompactEquivalence_commShift :
    (cohomologyCompactEquivalence k).functor.CommShift ℤ := by
  dsimp only [cohomologyCompactEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

instance cohomologyCompactEquivalence_isTriangulated :
    (cohomologyCompactEquivalence k).functor.IsTriangulated := by
  dsimp only [cohomologyCompactEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- D^b of finite-dimensional Kronecker modules is the compact module derived category. -/
def compactEquivalence := (equivalence k).trans (cohomologyCompactEquivalence k)

instance compactEquivalence_commShift : (compactEquivalence k).functor.CommShift ℤ := by
  change ((comparison k) ⋙ (cohomologyCompactEquivalence k).functor).CommShift ℤ
  infer_instance

instance compactEquivalence_isTriangulated : (compactEquivalence k).functor.IsTriangulated := by
  change ((comparison k) ⋙ (cohomologyCompactEquivalence k).functor).IsTriangulated
  infer_instance

instance compactEquivalence_inverseCommShift :
    (compactEquivalence k).inverse.CommShift ℤ := (compactEquivalence k).commShiftInverse ℤ

instance compactEquivalence_inverseIsTriangulated :
    (compactEquivalence k).inverse.IsTriangulated := by
  let E := compactEquivalence k
  let : E.toAdjunction.CommShift ℤ := E.toAdjunction.commShift_of_leftAdjoint ℤ
  exact E.toAdjunction.isTriangulated_rightAdjoint

#print axioms Beilinson.KroneckerBoundedDerived.compactEquivalence_inverseIsTriangulated
#print axioms Beilinson.KroneckerBoundedDerived.comparison_isTriangulated
#print axioms Beilinson.KroneckerBoundedDerived.compactEquivalence_isTriangulated
#print axioms Beilinson.KroneckerBoundedDerived.compactEquivalence
#print axioms Beilinson.KroneckerBoundedDerived.equivalence

end Beilinson.KroneckerBoundedDerived

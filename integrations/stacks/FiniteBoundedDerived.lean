module

public import Beilinson.FiniteModuleCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.Modules
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! The actual bounded derived category of finite-dimensional modules over a finite-dimensional algebra.
The finite free covers proved in the production library verify the Serre
subcategory comparison, rather than assuming a comparison of derived categories. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] isClosedUnderIsomorphisms_isCompactObject isTriangulated_isCompactObject

namespace Beilinson.FiniteBoundedDerived

universe u
open scoped ModuleCat.Algebra

variable (k : Type u) [Field k] (S : Type u) [Ring S] [Algebra k S] [Module.Finite k S]

abbrev finiteModules : ObjectProperty (ModuleCat.{u} S) :=
  FiniteModuleCategory.finiteModules k S

local instance finiteLimits : PreservesFiniteLimits (finiteModules k S).ι :=
  (finiteModules k S).preservesFiniteLimits_ι
local instance finiteColimits : PreservesFiniteColimits (finiteModules k S).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass (finiteModules k S)

private theorem covers {X Y : ModuleCat.{u} S}
    (f : X ⟶ Y) (hf : Epi f) (hY : finiteModules k S Y) :
    ∃ (P : ModuleCat.{u} S) (g : P ⟶ X),
      finiteModules k S P ∧ Epi (g ≫ f) := by
  let := hf
  exact FiniteModuleCategory.coversEpis k S f hY

private instance full_minus :
    (DerivedCategory.Minus.ι ⋙ (finiteModules k S).ι.mapDerivedCategory).Full :=
  (ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory (finiteModules k S) (fun {_ _} f hf hY => covers k S f hf hY)).1

private instance faithful_minus :
    (DerivedCategory.Minus.ι ⋙ (finiteModules k S).ι.mapDerivedCategory).Faithful :=
  (ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory (finiteModules k S) (fun {_ _} f hf hY => covers k S f hf hY)).2.1

private theorem bounded_le_minus :
    (DerivedCategory.TStructure.t (C := (finiteModules k S).FullSubcategory)).bounded ≤
      (DerivedCategory.TStructure.t (C := (finiteModules k S).FullSubcategory)).minus :=
  fun _ h => h.2

private instance full_bounded :
    (DerivedCategory.Bounded.ι ⋙ (finiteModules k S).ι.mapDerivedCategory).Full :=
  inferInstanceAs (ObjectProperty.ιOfLE (bounded_le_minus k S) ⋙
    (DerivedCategory.Minus.ι ⋙ (finiteModules k S).ι.mapDerivedCategory)).Full

private instance faithful_bounded :
    (DerivedCategory.Bounded.ι ⋙ (finiteModules k S).ι.mapDerivedCategory).Faithful :=
  inferInstanceAs (ObjectProperty.ιOfLE (bounded_le_minus k S) ⋙
    (DerivedCategory.Minus.ι ⋙ (finiteModules k S).ι.mapDerivedCategory)).Faithful

local instance boundedClosed :
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k S)).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryBBounded_isClosedUnderIsomorphisms _
    (WeakSerre.isWeakSerre_of_isWeakSerreClass (finiteModules k S))

/-- The canonical derived inclusion, restricted to bounded finite-dimensional cohomology. -/
def comparison : DerivedCategory.Bounded (finiteModules k S).FullSubcategory ⥤
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k S)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryBBounded (finiteModules k S)).lift
    (DerivedCategory.Bounded.ι ⋙ (finiteModules k S).ι.mapDerivedCategory) fun K =>
      ⟨⟨(DerivedCategoryB.isBoundedBelow_mapDerivedCategory_obj_iff _ K.obj).2
          ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K.obj).2 K.property.1),
        (DerivedCategoryB.isBoundedAbove_mapDerivedCategory_obj_iff _ K.obj).2
          ((DerivedCategoryB.isBoundedAbove_iff_exists_isLE K.obj).2 K.property.2)⟩,
        fun i => (finiteModules k S).prop_of_iso
          (((finiteModules k S).ι.mapDerivedCategoryHomologyIso i).app K.obj).symm
          ((DerivedCategory.homologyFunctor _ i).obj K.obj).property⟩

instance comparison_full : (comparison k S).Full where
  map_surjective f := by
    obtain ⟨g, hg⟩ := (DerivedCategory.Bounded.ι ⋙
      (finiteModules k S).ι.mapDerivedCategory).map_surjective f.hom
    exact ⟨g, ObjectProperty.hom_ext _ hg⟩

instance comparison_faithful : (comparison k S).Faithful where
  map_injective h := (DerivedCategory.Bounded.ι ⋙
    (finiteModules k S).ι.mapDerivedCategory).map_injective (congrArg (fun q => q.hom) h)

instance comparison_essSurj : (comparison k S).EssSurj where
  mem_essImage K := by
    have hK := (ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory
      (finiteModules k S) (fun {_ _} f hf hY => covers k S f hf hY)).2.2 K.obj
    obtain ⟨Y, ⟨e⟩⟩ := hK.mpr
      ⟨(DerivedCategoryB.isBoundedAbove_iff_exists_isLE _).mp K.property.1.2, K.property.2⟩
    have hb : DerivedCategoryB.IsBoundedBelow Y.obj :=
      (DerivedCategoryB.isBoundedBelow_mapDerivedCategory_obj_iff _ Y.obj).mp
        (DerivedCategoryB.isBoundedBelow_of_iso e.symm K.property.1.1)
    exact ⟨⟨Y.obj, (DerivedCategoryB.isBoundedBelow_iff_exists_isGE Y.obj).mp hb, Y.property⟩,
      ⟨ObjectProperty.isoMk _ e⟩⟩

instance comparison_isEquivalence : (comparison k S).IsEquivalence := {}

def equivalence : DerivedCategory.Bounded (finiteModules k S).FullSubcategory ≌
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k S)).FullSubcategory :=
  (comparison k S).asEquivalence

/-- Forgetting the cohomology condition gives the ordinary derived inclusion. -/
def comparisonCompInclusionIso : comparison k S ⋙
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k S)).ι ≅
      DerivedCategory.Bounded.ι ⋙ (finiteModules k S).ι.mapDerivedCategory := Iso.refl _

instance comparison_commShift : (comparison k S).CommShift ℤ :=
  Functor.CommShift.ofComp (comparisonCompInclusionIso k S) ℤ

instance comparisonCompInclusionIso_commShift :
    NatTrans.CommShift (comparisonCompInclusionIso k S).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance comparison_isTriangulated : (comparison k S).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (comparisonCompInclusionIso k S)).2 inferInstance

/-- A module-derived object is bounded exactly when its nonzero cohomology support is finite. -/
theorem bounded_iff_finite_support (K : DerivedCategory (ModuleCat.{u} S)) :
    DerivedCategoryB.IsBounded K ↔
      {i : ℤ | Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj K)}.Finite := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    apply (Set.finite_Icc a b).subset
    intro i hi
    have hlo : a ≤ i := by
      by_contra h
      have hz := ha i (by omega)
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      exact not_nontrivial _ hi
    have hhi : i ≤ b := by
      by_contra h
      have hz := hb i (by omega)
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      exact not_nontrivial _ hi
    exact ⟨hlo, hhi⟩
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    constructor
    · refine ⟨a, fun i hi => ModuleCat.isZero_iff_subsingleton.mpr ?_⟩
      apply not_nontrivial_iff_subsingleton.mp
      intro hn
      have := ha hn
      omega
    · refine ⟨b, fun i hi => ModuleCat.isZero_iff_subsingleton.mpr ?_⟩
      apply not_nontrivial_iff_subsingleton.mp
      intro hn
      have := hb hn
      omega

/-- Bounded finite-dimensional cohomology is the finite-total-cohomology condition. -/
theorem bounded_iff_finite_total (K : DerivedCategory (ModuleCat.{u} S)) :
    DerivedCategoryB.derivedCategoryBBounded (finiteModules k S) K ↔
      ((∀ i : ℤ, finiteModules k S ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj K)) ∧
        {i : ℤ | Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj K)}.Finite) := by
  change (DerivedCategoryB.IsBounded K ∧ _) ↔ _
  rw [bounded_iff_finite_support S K]
  exact and_comm

variable (hcompact : ∀ K : DerivedCategory (ModuleCat.{u} S),
  DerivedCategoryB.derivedCategoryBBounded (finiteModules k S) K ↔ IsCompactObject.{u} K)

/-- Repackage the checked cohomology criterion as an equivalence of subcategories. -/
def cohomologyCompactEquivalence :
    (DerivedCategoryB.derivedCategoryBBounded (finiteModules k S)).FullSubcategory ≌
      ObjectProperty.FullSubcategory (IsCompactObject.{u}
        (C := DerivedCategory (ModuleCat.{u} S))) :=
  (CategoryTheory.Equivalence.refl
    (C := DerivedCategory (ModuleCat.{u} S))).congrFullSubcategory (by
    funext K
    exact propext (hcompact K).symm)

instance cohomologyCompactEquivalence_commShift :
    (cohomologyCompactEquivalence k S hcompact).functor.CommShift ℤ := by
  dsimp only [cohomologyCompactEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

instance cohomologyCompactEquivalence_isTriangulated :
    (cohomologyCompactEquivalence k S hcompact).functor.IsTriangulated := by
  dsimp only [cohomologyCompactEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- D^b of finite-dimensional modules is the compact module derived category. -/
def compactEquivalence := (equivalence k S).trans (cohomologyCompactEquivalence k S hcompact)

instance compactEquivalence_commShift : (compactEquivalence k S hcompact).functor.CommShift ℤ := by
  change ((comparison k S) ⋙ (cohomologyCompactEquivalence k S hcompact).functor).CommShift ℤ
  infer_instance

instance compactEquivalence_isTriangulated : (compactEquivalence k S hcompact).functor.IsTriangulated := by
  change ((comparison k S) ⋙ (cohomologyCompactEquivalence k S hcompact).functor).IsTriangulated
  infer_instance

instance compactEquivalence_inverseCommShift :
    (compactEquivalence k S hcompact).inverse.CommShift ℤ := (compactEquivalence k S hcompact).commShiftInverse ℤ

instance compactEquivalence_inverseIsTriangulated :
    (compactEquivalence k S hcompact).inverse.IsTriangulated := by
  let E := compactEquivalence k S hcompact
  let : E.toAdjunction.CommShift ℤ := E.toAdjunction.commShift_of_leftAdjoint ℤ
  exact E.toAdjunction.isTriangulated_rightAdjoint

#print axioms Beilinson.FiniteBoundedDerived.bounded_iff_finite_total
#print axioms Beilinson.FiniteBoundedDerived.compactEquivalence_inverseIsTriangulated
#print axioms Beilinson.FiniteBoundedDerived.comparison_isTriangulated
#print axioms Beilinson.FiniteBoundedDerived.compactEquivalence_isTriangulated
#print axioms Beilinson.FiniteBoundedDerived.compactEquivalence
#print axioms Beilinson.FiniteBoundedDerived.equivalence

end Beilinson.FiniteBoundedDerived

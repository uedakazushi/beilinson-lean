module

public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import GeometricPerfectProbe
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.BoundedCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.Modules
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel

/-! Compare bounded coherent cohomology with the bounded derived category of
coherent sheaves, explicitly transporting the chosen derived-category model. -/

set_option autoImplicit false

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open StacksDraft.DerivedModel

namespace Beilinson.CoherentDerivedComparison

universe u v w z

section Models
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Boundedness is preserved by the comparison of derived-category models. -/
theorem bounded_model_iff (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)
    (K : @DerivedCategory C _ _ h₁) :
    @DerivedCategoryB.IsBounded C _ _ h₂ ((modelEquiv h₁ h₂).functor.obj K) ↔
      @DerivedCategoryB.IsBounded C _ _ h₁ K := by
  have hz (n : ℤ) :
      IsZero ((@DerivedCategory.homologyFunctor C _ _ h₂ n).obj
        ((modelEquiv h₁ h₂).functor.obj K)) ↔
      IsZero ((@DerivedCategory.homologyFunctor C _ _ h₁ n).obj K) :=
    (modelHomologyFunctorIso h₁ h₂ n).app K |>.isZero_iff
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, fun i hi => (hz i).mp (ha i hi)⟩,
      ⟨b, fun i hi => (hz i).mp (hb i hi)⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, fun i hi => (hz i).mpr (ha i hi)⟩,
      ⟨b, fun i hi => (hz i).mpr (hb i hi)⟩⟩

/-- The bounded subcategory with specified cohomology is independent of the model. -/
def boundedModelEquiv (B : ObjectProperty C) [B.IsClosedUnderIsomorphisms]
    (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C) :
    (@DerivedCategoryB.derivedCategoryBBounded C _ _ h₁ B).FullSubcategory ≌
      (@DerivedCategoryB.derivedCategoryBBounded C _ _ h₂ B).FullSubcategory := by
  letI : (@DerivedCategoryB.derivedCategoryBBounded C _ _ h₂ B).IsClosedUnderIsomorphisms :=
    ⟨fun e hK => ⟨DerivedCategoryB.isBounded_of_iso e hK.1,
      fun n => B.prop_of_iso ((@DerivedCategory.homologyFunctor C _ _ h₂ n).mapIso e)
        (hK.2 n)⟩⟩
  exact (modelEquiv h₁ h₂).congrFullSubcategory (funext fun K => propext
    (and_congr (bounded_model_iff h₁ h₂ K)
      (derivedCategoryB_modelEquiv_functor_obj_iff B h₁ h₂ K)))

end Models

instance coherentWeakSerre (X : Scheme.{u}) :
    ObjectProperty.IsWeakSerreClass (fun M : X.Modules => M.IsCoherent) :=
  inferInstanceAs (coherentInModules X).IsWeakSerreClass

instance smallBoundedTriangulated (X : Scheme.{u}) :
    (@DerivedCategoryB.derivedCategoryBBounded X.Modules _ _
      (Scheme.Modules.hasDerivedCategory X) (fun M => M.IsCoherent)).IsTriangulated := by
  let := Scheme.Modules.hasDerivedCategory X
  exact DerivedCategoryB.isTriangulated_derivedCategoryBBounded
    (fun M : X.Modules => M.IsCoherent)

instance smallBoundedClosed (X : Scheme.{u}) :
    (@DerivedCategoryB.derivedCategoryBBounded X.Modules _ _
      (Scheme.Modules.hasDerivedCategory X) (fun M => M.IsCoherent)).IsClosedUnderIsomorphisms := by
  let := Scheme.Modules.hasDerivedCategory X
  exact DerivedCategoryB.derivedCategoryBBounded_isClosedUnderIsomorphisms _
    (WeakSerre.isWeakSerre_of_isWeakSerreClass (fun M : X.Modules => M.IsCoherent))

section SmallAmbient
attribute [local instance 10000] SheafOfModules.hasDerivedCategory Scheme.Modules.hasDerivedCategory
instance smallBounded_shift_additive (X : Scheme.{u}) (n : ℤ) :
    (shiftFunctor (DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.Modules => M.IsCoherent)).FullSubcategory n).Additive := by infer_instance
instance smallDerived_shift_additive (X : Scheme.{u}) (n : ℤ) :
    (shiftFunctor (DerivedCategory X.Modules) n).Additive := by infer_instance
instance smallBounded_pretriangulated (X : Scheme.{u}) :
    Pretriangulated (DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.Modules => M.IsCoherent)).FullSubcategory := by infer_instance
end SmallAmbient

section Schemes

attribute [local instance 10000] HasDerivedCategory.standard

/-- The actual bounded derived category of coherent sheaves, transported to the
locally small model used by the geometric Beilinson functor. -/
def coherentEquivalence (X : Scheme.{u}) [IsNoetherian X] :
    DerivedCategory.Bounded (SheafOfModules.CoherentModules X.ringCatSheaf) ≌
      (@DerivedCategoryB.derivedCategoryBBounded X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) (fun M => M.IsCoherent)).FullSubcategory :=
  (coherentToModulesDerivedBoundedEquivalence X).trans
    (boundedModelEquiv (coherentInModules X) (HasDerivedCategory.standard _)
      (Scheme.Modules.hasDerivedCategory X))

/-- Fix the standard model on both ends of the derived inclusion. -/
def canonicalDerivedInclusion (X : Scheme.{u}) :
    DerivedCategory (SheafOfModules.CoherentModules X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  (coherentInModules X).ι.mapDerivedCategory

instance canonicalDerivedInclusion_commShift (X : Scheme.{u}) :
    (canonicalDerivedInclusion X).CommShift ℤ := by
  dsimp only [canonicalDerivedInclusion]
  infer_instance

instance canonicalDerivedInclusion_isTriangulated (X : Scheme.{u}) :
    (canonicalDerivedInclusion X).IsTriangulated := by
  dsimp only [canonicalDerivedInclusion]
  infer_instance

/-- Pin both universe levels before composing with the model comparison. -/
def modelComparison (X : Scheme.{u}) :
    @DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) _ _ (HasDerivedCategory.standard _) ≌
      @DerivedCategory X.Modules _ _ (Scheme.Modules.hasDerivedCategory X) :=
  modelEquiv (C := SheafOfModules.{u} X.ringCatSheaf)
    (HasDerivedCategory.standard _) (Scheme.Modules.hasDerivedCategory X)

instance modelComparison_commShift (X : Scheme.{u}) :
    (modelComparison X).functor.CommShift ℤ :=
  StacksDraft.Perfect.derivedEquivalenceCommShift _ _

instance modelComparison_isTriangulated (X : Scheme.{u}) :
    (modelComparison X).functor.IsTriangulated :=
  StacksDraft.Perfect.derivedEquivalence_isTriangulated _ _

def coherentCompInclusionIso (X : Scheme.{u}) [IsNoetherian X] :
    (coherentEquivalence X).functor ⋙
      (@DerivedCategoryB.derivedCategoryBBounded X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) (fun M => M.IsCoherent)).ι ≅
    DerivedCategory.Bounded.ι ⋙ canonicalDerivedInclusion X ⋙
      (modelComparison X).functor := Iso.refl _

attribute [local instance] StacksDraft.Perfect.derivedEquivalenceCommShift
  StacksDraft.Perfect.derivedEquivalence_isTriangulated

instance coherentEquivalence_commShift (X : Scheme.{u}) [IsNoetherian X] :
    (coherentEquivalence X).functor.CommShift ℤ :=
  Functor.CommShift.ofComp (coherentCompInclusionIso X) ℤ

instance coherentCompInclusionIso_commShift (X : Scheme.{u}) [IsNoetherian X] :
    NatTrans.CommShift (coherentCompInclusionIso X).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance coherentEquivalence_isTriangulated (X : Scheme.{u}) [IsNoetherian X] :
    (coherentEquivalence X).functor.IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (coherentCompInclusionIso X)).2 inferInstance

end Schemes

section QuasiCoherent

attribute [local instance 10000] SheafOfModules.hasDerivedCategory
  Scheme.Modules.hasDerivedCategory

/-- Bounded coherent cohomology, as a property of D_QCoh objects. -/
abbrev boundedCoherent (X : Scheme.{u}) :
    ObjectProperty (Stacks.Duality.quasiCoherentDerivedCategory X) :=
  fun K => DerivedCategoryB.derivedCategoryBBounded (fun M : X.Modules => M.IsCoherent) K.obj

instance boundedCoherent_triangulated (X : Scheme.{u}) :
    (boundedCoherent X).IsTriangulated :=
  inferInstanceAs ((DerivedCategoryB.derivedCategoryBBounded
    (fun M : X.Modules => M.IsCoherent)).inverseImage
      (DerivedCategoryB.derivedCategoryB
        (show ObjectProperty X.Modules from SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι).IsTriangulated

instance boundedCoherent_shift_additive (X : Scheme.{u}) (n : ℤ) :
    (shiftFunctor (boundedCoherent X).FullSubcategory n).Additive := by infer_instance

instance boundedCoherent_pretriangulated (X : Scheme.{u}) :
    Pretriangulated (boundedCoherent X).FullSubcategory := by infer_instance

/-- Coherent cohomology is automatically quasi-coherent. -/
def ambientToQuasiCoherent (X : Scheme.{u}) :
    (DerivedCategoryB.derivedCategoryBBounded (fun M : X.Modules => M.IsCoherent)).FullSubcategory ⥤
      (boundedCoherent X).FullSubcategory where
  obj K := by
    have hc (n : ℤ) := K.property.2 n
    exact ⟨⟨K.obj, fun n => by
      let := hc n
      exact isQuasicoherent_of_isCoherent _⟩, K.property⟩
  map f := ⟨⟨f.hom⟩⟩

/-- Forgetting the redundant quasi-coherence condition. -/
def quasiCoherentToAmbient (X : Scheme.{u}) :
    (boundedCoherent X).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBBounded (fun M : X.Modules => M.IsCoherent)).FullSubcategory where
  obj K := ⟨K.obj.obj, K.property⟩
  map f := ⟨f.hom.hom⟩

/-- The two ways of locating the bounded coherent subcategory agree. -/
def ambientEquivalence (X : Scheme.{u}) :
    (DerivedCategoryB.derivedCategoryBBounded (fun M : X.Modules => M.IsCoherent)).FullSubcategory ≌
      (boundedCoherent X).FullSubcategory where
  functor := ambientToQuasiCoherent X
  inverse := quasiCoherentToAmbient X
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp K := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    change (𝟙 K.obj) ≫ (𝟙 K.obj) = 𝟙 K.obj
    exact Category.id_comp _

instance ambientEquivalence_commShift (X : Scheme.{u}) :
    (ambientEquivalence X).functor.CommShift ℤ :=
  Functor.CommShift.ofComp (F := (ambientEquivalence X).functor) (G := (boundedCoherent X).ι ⋙
    (DerivedCategoryB.derivedCategoryB
      (show ObjectProperty X.Modules from SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι)
    (H := (DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.Modules => M.IsCoherent)).ι) (Iso.refl _) ℤ

instance ambientEquivalence_isTriangulated (X : Scheme.{u}) :
    (ambientEquivalence X).functor.IsTriangulated := by
  let G := (boundedCoherent X).ι ⋙ (DerivedCategoryB.derivedCategoryB
    (show ObjectProperty X.Modules from SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι
  let H := (DerivedCategoryB.derivedCategoryBBounded
    (fun M : X.Modules => M.IsCoherent)).ι
  let e : (ambientEquivalence X).functor ⋙ G ≅ H := Iso.refl _
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

end QuasiCoherent

section Final
attribute [local instance 10000] HasDerivedCategory.standard

/-- D^b(Coh X) equals the bounded-coherent full subcategory used by Beilinson. -/
def equivalence (X : Scheme.{u}) [IsNoetherian X] :
    DerivedCategory.Bounded (SheafOfModules.CoherentModules X.ringCatSheaf) ≌
      (boundedCoherent X).FullSubcategory :=
  (coherentEquivalence X).trans (ambientEquivalence X)

instance equivalence_commShift (X : Scheme.{u}) [IsNoetherian X] :
    (equivalence X).functor.CommShift ℤ := by
  change ((coherentEquivalence X).functor ⋙ (ambientEquivalence X).functor).CommShift ℤ
  infer_instance

instance equivalence_isTriangulated (X : Scheme.{u}) [IsNoetherian X] :
    (equivalence X).functor.IsTriangulated := by
  change ((coherentEquivalence X).functor ⋙ (ambientEquivalence X).functor).IsTriangulated
  infer_instance

instance equivalence_inverseCommShift (X : Scheme.{u}) [IsNoetherian X] :
    (equivalence X).inverse.CommShift ℤ := (equivalence X).commShiftInverse ℤ

instance equivalence_inverseIsTriangulated (X : Scheme.{u}) [IsNoetherian X] :
    (equivalence X).inverse.IsTriangulated := by
  let E := equivalence X
  let : E.toAdjunction.CommShift ℤ := E.toAdjunction.commShift_of_leftAdjoint ℤ
  exact E.toAdjunction.isTriangulated_rightAdjoint

end Final

#print axioms Beilinson.CoherentDerivedComparison.equivalence_commShift
#print axioms Beilinson.CoherentDerivedComparison.equivalence_isTriangulated
#print axioms Beilinson.CoherentDerivedComparison.equivalence_inverseIsTriangulated
#print axioms Beilinson.CoherentDerivedComparison.equivalence
#print axioms Beilinson.CoherentDerivedComparison.coherentEquivalence
#print axioms Beilinson.CoherentDerivedComparison.bounded_model_iff
#print axioms Beilinson.CoherentDerivedComparison.boundedModelEquiv

end Beilinson.CoherentDerivedComparison

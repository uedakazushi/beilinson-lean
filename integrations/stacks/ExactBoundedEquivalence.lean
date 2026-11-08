module

public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryBounded
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! An exact equivalence of abelian categories induces a triangulated equivalence
of their actual bounded derived categories, at the chosen derived models. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Beilinson.ExactBoundedEquivalence

universe u v w u' v' w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]

/-- The induced unbounded equivalence, using the actual exact functors. -/
def derived : DerivedCategory C ≌ DerivedCategory D :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence e

private theorem map_bounded (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (hK : (DerivedCategory.TStructure.t (C := C)).bounded K) :
    (DerivedCategory.TStructure.t (C := D)).bounded (F.mapDerivedCategory.obj K) :=
  (F.mapDerivedCategoryBounded.obj ⟨K, hK⟩).property

/-- The unbounded exact equivalence preserves and reflects the bounded subcategories. -/
theorem bounded_iff (K : DerivedCategory C) :
    (DerivedCategory.TStructure.t (C := D)).bounded ((derived e).functor.obj K) ↔
      (DerivedCategory.TStructure.t (C := C)).bounded K := by
  constructor
  · intro h
    have h' := map_bounded e.inverse ((derived e).functor.obj K) h
    exact ((DerivedCategory.TStructure.t (C := C)).bounded).prop_of_iso
      ((derived e).unitIso.app K).symm h'
  · exact map_bounded e.functor K

/-- The actual bounded derived categories of exactly equivalent abelian categories. -/
def equivalence : DerivedCategory.Bounded C ≌ DerivedCategory.Bounded D :=
  (derived e).congrFullSubcategory (by
    funext K
    exact propext (bounded_iff e K))

instance derived_commShift : (derived e).functor.CommShift ℤ :=
  inferInstanceAs (e.functor.mapDerivedCategory.CommShift ℤ)

instance derived_isTriangulated : (derived e).functor.IsTriangulated :=
  inferInstanceAs (e.functor.mapDerivedCategory.IsTriangulated)

instance equivalence_commShift : (equivalence e).functor.CommShift ℤ := by
  dsimp only [equivalence, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

instance equivalence_isTriangulated : (equivalence e).functor.IsTriangulated := by
  dsimp only [equivalence, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

instance equivalence_inverseCommShift : (equivalence e).inverse.CommShift ℤ :=
  (equivalence e).commShiftInverse ℤ

instance equivalence_inverseIsTriangulated : (equivalence e).inverse.IsTriangulated := by
  let E := equivalence e
  let : E.toAdjunction.CommShift ℤ := E.toAdjunction.commShift_of_leftAdjoint ℤ
  exact E.toAdjunction.isTriangulated_rightAdjoint

#print axioms equivalence
#print axioms equivalence_inverseIsTriangulated

end Beilinson.ExactBoundedEquivalence

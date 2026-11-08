module

public import Beilinson.FiniteModuleCategory
public import ExactBoundedEquivalence

/-! A coefficient-algebra isomorphism induces an equivalence of actual finite
module categories and of their own bounded derived categories. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance 10000] HasDerivedCategory.standard

namespace Beilinson.FiniteScalarEquivalence

universe u
variable {k : Type u} [Field k] {S T : Type u} [Ring S] [Ring T]
variable [Algebra k S] [Algebra k T] (e : S ≃ₐ[k] T)

/-- Change from S-modules to T-modules along the inverse algebra isomorphism. -/
abbrev changeRing : ModuleCat.{u} S ⥤ ModuleCat.{u} T :=
  ModuleCat.restrictScalars e.symm.toRingEquiv.toRingHom

/-- The coefficient vector spaces are naturally the same under this ring change. -/
def coefficientIso (M : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars (algebraMap k S)).obj M ≅
      (ModuleCat.restrictScalars (algebraMap k T)).obj ((changeRing e).obj M) :=
  (show (ModuleCat.restrictScalars (algebraMap k S)).obj M ≃ₗ[k]
      (ModuleCat.restrictScalars (algebraMap k T)).obj ((changeRing e).obj M) from
    { toEquiv := Equiv.refl _
      map_add' _ _ := rfl
      map_smul' a x := by
        change (algebraMap k S a) • x = e.symm (algebraMap k T a) • x
        rw [e.symm.commutes] }).toModuleIso

/-- Finiteness over the field is preserved and reflected, not assumed invariant under ring isomorphisms. -/
theorem finite_iff (M : ModuleCat.{u} S) :
    FiniteModuleCategory.finiteModules k T ((changeRing e).obj M) ↔
      FiniteModuleCategory.finiteModules k S M := by
  constructor
  · intro h
    let : Module.Finite k
        ((ModuleCat.restrictScalars (algebraMap k T)).obj ((changeRing e).obj M)) := h
    exact Module.Finite.equiv (coefficientIso e M).symm.toLinearEquiv
  · intro h
    let : Module.Finite k ((ModuleCat.restrictScalars (algebraMap k S)).obj M) := h
    exact Module.Finite.equiv (coefficientIso e M).toLinearEquiv

/-- The actual finite-dimensional module categories are equivalent. -/
def finiteEquivalence : (FiniteModuleCategory.finiteModules k S).FullSubcategory ≌
    (FiniteModuleCategory.finiteModules k T).FullSubcategory :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm.toRingEquiv).congrFullSubcategory (by
    funext M
    exact propext (finite_iff e M))

instance finiteEquivalence_additive : (finiteEquivalence e).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance finiteEquivalence_inverseAdditive : (finiteEquivalence e).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The actual bounded derived categories of finite-dimensional modules are equivalent. -/
def boundedEquivalence := ExactBoundedEquivalence.equivalence (finiteEquivalence e)

instance boundedEquivalence_commShift : (boundedEquivalence e).functor.CommShift ℤ :=
  inferInstanceAs ((ExactBoundedEquivalence.equivalence (finiteEquivalence e)).functor.CommShift ℤ)

instance boundedEquivalence_isTriangulated : (boundedEquivalence e).functor.IsTriangulated :=
  inferInstanceAs ((ExactBoundedEquivalence.equivalence (finiteEquivalence e)).functor.IsTriangulated)

instance boundedEquivalence_inverseCommShift : (boundedEquivalence e).inverse.CommShift ℤ :=
  inferInstanceAs ((ExactBoundedEquivalence.equivalence (finiteEquivalence e)).inverse.CommShift ℤ)

instance boundedEquivalence_inverseIsTriangulated : (boundedEquivalence e).inverse.IsTriangulated :=
  inferInstanceAs ((ExactBoundedEquivalence.equivalence (finiteEquivalence e)).inverse.IsTriangulated)

#print axioms coefficientIso
#print axioms finiteEquivalence
#print axioms boundedEquivalence
#print axioms boundedEquivalence_inverseIsTriangulated

end Beilinson.FiniteScalarEquivalence

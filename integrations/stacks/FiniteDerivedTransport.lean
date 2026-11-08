module

public import FiniteScalarEquivalence
public import FiniteBoundedDerived

/-! Transfer bounded finite-dimensional cohomology and compactness along an algebra isomorphism. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

namespace Beilinson.FiniteDerivedTransport

universe u
variable {k : Type u} [Field k] {S T : Type u} [Ring S] [Ring T]
variable [Algebra k S] [Algebra k T] (e : S ≃ₐ[k] T)

def ambientEquivalence : ModuleCat.{u} S ≌ ModuleCat.{u} T :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm.toRingEquiv

instance ambient_additive : (ambientEquivalence e).functor.Additive :=
  inferInstanceAs (FiniteScalarEquivalence.changeRing e).Additive

instance ambient_inverse_additive : (ambientEquivalence e).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

def derivedEquivalence := ExactBoundedEquivalence.derived (ambientEquivalence e)

instance derived_additive : (derivedEquivalence e).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

def cohomologyIso (K : DerivedCategory (ModuleCat.{u} S)) (q : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} T) q).obj
        ((derivedEquivalence e).functor.obj K) ≅
      (ambientEquivalence e).functor.obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) q).obj K) :=
  ((ambientEquivalence e).functor.mapDerivedCategoryHomologyIso q).app K

theorem finite_cohomology_iff (K : DerivedCategory (ModuleCat.{u} S)) (q : ℤ) :
    FiniteModuleCategory.finiteModules k T
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) q).obj
          ((derivedEquivalence e).functor.obj K)) ↔
      FiniteModuleCategory.finiteModules k S
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) q).obj K) :=
  ((FiniteModuleCategory.finiteModules k T).prop_iff_of_iso (cohomologyIso e K q)).trans
    (FiniteScalarEquivalence.finite_iff e _)

theorem nontrivial_cohomology_iff (K : DerivedCategory (ModuleCat.{u} S)) (q : ℤ) :
    Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) q).obj
      ((derivedEquivalence e).functor.obj K)) ↔
    Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) q).obj K) :=
  (cohomologyIso e K q).toLinearEquiv.nontrivial_congr

variable [Module.Finite k S] [Module.Finite k T]

/-- The finite-total-cohomology description avoids dependence on chosen bounds. -/
theorem boundedFinite_iff (K : DerivedCategory (ModuleCat.{u} S)) :
    DerivedCategoryB.derivedCategoryBBounded (FiniteModuleCategory.finiteModules k T)
        ((derivedEquivalence e).functor.obj K) ↔
      DerivedCategoryB.derivedCategoryBBounded (FiniteModuleCategory.finiteModules k S) K := by
  rw [FiniteBoundedDerived.bounded_iff_finite_total k T,
    FiniteBoundedDerived.bounded_iff_finite_total k S]
  refine and_congr (forall_congr' (finite_cohomology_iff e K)) ?_
  have hs : {q : ℤ | Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) q).obj
      ((derivedEquivalence e).functor.obj K))} =
      {q : ℤ | Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) q).obj K)} :=
    Set.ext (nontrivial_cohomology_iff e K)
  rw [hs]

/-- A checked compactness criterion transports to any isomorphic coefficient algebra. -/
theorem bounded_iff_compact (e : S ≃ₐ[k] T)
    (hT : ∀ K : DerivedCategory (ModuleCat.{u} T),
      DerivedCategoryB.derivedCategoryBBounded (FiniteModuleCategory.finiteModules k T) K ↔
        IsCompactObject.{u} K)
    (K : DerivedCategory (ModuleCat.{u} S)) :
    DerivedCategoryB.derivedCategoryBBounded (FiniteModuleCategory.finiteModules k S) K ↔
      IsCompactObject.{u} K :=
  (boundedFinite_iff e K).symm.trans ((hT _).trans
    (isCompactObject_iff_isCompactObject_obj (derivedEquivalence e).functor K).symm)

#print axioms boundedFinite_iff
#print axioms bounded_iff_compact

end Beilinson.FiniteDerivedTransport

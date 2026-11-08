module

public import CoherentTensor
public import ExactBoundedEquivalence
public import CoherentDerivedComparison

/-! The actual bounded derived autoequivalence of coherent modules obtained by
tensoring with an invertible sheaf. The forward functor is the induced exact tensor functor. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

namespace Beilinson.CoherentTensorBounded

universe u
variable (X : Scheme.{u}) (L : X.Modules)
variable [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

instance forward_additive : (CoherentTensor.equivalence X L).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance inverse_additive : (CoherentTensor.equivalence X L).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Tensor with L on the actual bounded derived category of coherent modules. -/
def equivalence :
    DerivedCategory.Bounded (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) ≌
      DerivedCategory.Bounded (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :=
  ExactBoundedEquivalence.equivalence (CoherentTensor.equivalence X L)

/-- The forward equivalence is induced by the actual restricted tensor functor. -/
theorem equivalence_functor : (equivalence X L).functor =
    (CoherentTensor.equivalence X L).functor.mapDerivedCategoryBounded := rfl

instance equivalence_commShift : (equivalence X L).functor.CommShift ℤ :=
  inferInstanceAs ((ExactBoundedEquivalence.equivalence
    (CoherentTensor.equivalence X L)).functor.CommShift ℤ)

instance equivalence_isTriangulated : (equivalence X L).functor.IsTriangulated :=
  inferInstanceAs ((ExactBoundedEquivalence.equivalence
    (CoherentTensor.equivalence X L)).functor.IsTriangulated)

instance equivalence_inverseCommShift : (equivalence X L).inverse.CommShift ℤ :=
  inferInstanceAs ((ExactBoundedEquivalence.equivalence
    (CoherentTensor.equivalence X L)).inverse.CommShift ℤ)

instance equivalence_inverseIsTriangulated : (equivalence X L).inverse.IsTriangulated :=
  inferInstanceAs ((ExactBoundedEquivalence.equivalence
    (CoherentTensor.equivalence X L)).inverse.IsTriangulated)

/-- Finite biproducts of coherent modules are coherent. -/
theorem coherent_biproduct {r : ℕ} (F : Fin r → X.Modules) [HasBiproduct F]
    (hF : ∀ i, (F i).IsCoherent) : (⨁ F).IsCoherent :=
  AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
    ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_of_iso
      (biproduct.isoCoproduct F).symm
      (Stacks.SheafOfModules.isCoherent_sigma _ fun i =>
        AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent (hF i)))

/-- A coherent module placed in degree zero, in its own bounded derived category. -/
def single (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    DerivedCategory.Bounded (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj M, ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩⟩

/-- An isomorphism of coherent modules induces one between their degree-zero objects in D^b. -/
def singleMapIso {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (e : M ≅ N) : single X M ≅ single X N :=
  ObjectProperty.isoMk _ ((DerivedCategory.singleFunctor _ 0).mapIso e)

/-- The bounded tensor equivalence agrees with tensoring coherent modules in degree zero. -/
def singleIso (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (equivalence X L).functor.obj (single X M) ≅
      single X ((CoherentTensor.equivalence X L).functor.obj M) :=
  ObjectProperty.isoMk _
    (((CoherentTensor.equivalence X L).functor.mapDerivedCategorySingleFunctor 0).app M)

#print axioms singleIso
#print axioms equivalence
#print axioms equivalence_functor
#print axioms equivalence_inverseIsTriangulated

end Beilinson.CoherentTensorBounded

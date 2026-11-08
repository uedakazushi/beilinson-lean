module

public import CoherentTensorBounded
public import ExactFunctorModels

/-! Tensoring with an invertible module on any chosen derived model of all
modules, and compatibility of that functor with the actual coherent inclusion. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace Beilinson.TensorDerivedModels

universe u w
variable (X : Scheme.{u})

/-- Pin the actual coherent category before forming derived functor composites. -/
def inclusion : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤ X.Modules :=
  (coherentInModules X).ι

local instance coherentDerivedCategory :
    HasDerivedCategory (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :=
  HasDerivedCategory.standard _

local instance coherentWeakSerre : (coherentInModules X).IsWeakSerreClass :=
  CoherentDerivedComparison.coherentWeakSerre X

local instance inclusionFiniteLimits : PreservesFiniteLimits (inclusion X) :=
  (coherentInModules X).preservesFiniteLimits_ι_of_isWeakSerreClass

local instance inclusionFiniteColimits : PreservesFiniteColimits (inclusion X) :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass (coherentInModules X)

local instance inclusionAdditive : (inclusion X).Additive where
  map_add := by intros; rfl

variable (L : X.Modules)
variable [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- The actual tensor equivalence on all modules, before passing to derived categories. -/
def modulesEquivalence : X.Modules ≌ X.Modules := (CoherentTensor.tensorFunctor X L).asEquivalence

instance modulesEquivalence_additive : (modulesEquivalence X L).functor.Additive :=
  inferInstanceAs ((CoherentTensor.tensorFunctor X L).Additive)

instance modulesEquivalence_inverseAdditive : (modulesEquivalence X L).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

local instance coherentFunctorAdditive : (CoherentTensor.functor X L).Additive :=
  CoherentTensorBounded.forward_additive X L

/-- The coherent tensor functor is literally the restriction of tensoring all modules. -/
def inclusionTensorIso : inclusion X ⋙ CoherentTensor.tensorFunctor X L ≅
    CoherentTensor.functor X L ⋙ inclusion X := Iso.refl _

variable [h : HasDerivedCategory.{w} X.Modules]

/-- The standard coherent inclusion and the direct inclusion into the chosen
ambient model agree after the canonical change of model. -/
def derivedInclusionModelIso :
    CoherentDerivedComparison.canonicalDerivedInclusion X ⋙
      (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard X.Modules) h).functor ≅
    (inclusion X).mapDerivedCategory :=
  ExactFunctorModels.targetModelIso (inclusion X) (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) h

/-- The unbounded derived tensor equivalence, using the supplied model of D(Mod O_X). -/
def derivedEquivalence : DerivedCategory X.Modules ≌ DerivedCategory X.Modules :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (modulesEquivalence X L)

instance derivedEquivalence_commShift : (derivedEquivalence X L).functor.CommShift ℤ :=
  inferInstanceAs ((CoherentTensor.tensorFunctor X L).mapDerivedCategory.CommShift ℤ)

instance derivedEquivalence_isTriangulated : (derivedEquivalence X L).functor.IsTriangulated :=
  inferInstanceAs ((CoherentTensor.tensorFunctor X L).mapDerivedCategory.IsTriangulated)

/-- The same square commutes after deriving, with the chosen ambient derived model. -/
def derivedInclusionTensorIso :
    ((inclusion X).mapDerivedCategory ⋙ (derivedEquivalence X L).functor) ≅
      ((CoherentTensor.functor X L).mapDerivedCategory ⋙ (inclusion X).mapDerivedCategory) :=
  Dualizing.mapDerivedCategoryCompNatIso (inclusion X) (CoherentTensor.tensorFunctor X L)
      (CoherentTensor.functor X L ⋙ inclusion X) (inclusionTensorIso X L) ≪≫
    Dualizing.mapDerivedCategoryComp (CoherentTensor.functor X L) (inclusion X)

#print axioms derivedEquivalence
#print axioms derivedInclusionModelIso
#print axioms derivedInclusionTensorIso

end Beilinson.TensorDerivedModels

module

public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.TensorExact
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.FinCases

/-! Tensoring with an invertible sheaf restricts to an equivalence of coherent
modules. Essential surjectivity uses an inverse tensor power, retaining coherence. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Beilinson.CoherentTensor

universe u
variable (X : Scheme.{u}) (L : X.Modules)
variable [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

abbrev coherentProperty : ObjectProperty X.Modules := fun M => M.IsCoherent

/-- Right tensoring with the chosen invertible sheaf. -/
def tensorFunctor : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf).flip.obj L

instance tensorFunctor_isEquivalence : (tensorFunctor X L).IsEquivalence := by
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf X.ringCatSheaf.2 L).2 inferInstance
  exact Stacks.ProjTwistFunctor.isEquivalence_tensorRightFunctor_of_isInvertible X.presheaf X.ringCatSheaf.2 L

instance tensorFunctor_additive : (tensorFunctor X L).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Tensoring with an invertible sheaf preserves coherence. -/
theorem coherent_obj (M : X.Modules) [M.IsCoherent] :
    ((tensorFunctor X L).obj M).IsCoherent :=
  AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X M L

/-- Restrict the actual tensor functor to coherent modules. -/
def functor : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  (coherentProperty X).lift
    ((coherentProperty X).ι ⋙ tensorFunctor X L)
    (fun M => coherent_obj X L M.obj)

instance functor_full : (functor X L).Full where
  map_surjective {M N} f := by
    obtain ⟨g, hg⟩ := (tensorFunctor X L).map_surjective f.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg

instance functor_faithful : (functor X L).Faithful where
  map_injective {M N} f g h := by
    apply ObjectProperty.hom_ext
    apply (tensorFunctor X L).map_injective
    exact congrArg (fun f : (functor X L).obj M ⟶ (functor X L).obj N => f.hom) h

instance functor_essSurj : (functor X L).EssSurj := by
  constructor
  intro M
  let family : Fin 1 → X.Modules := fun _ => L
  let : ∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible
      X.presheaf X.ringCatSheaf.2 (family i) := fun _ => inferInstance
  let v : Fin 1 → ℤ := fun _ => -1
  let N := AlgebraicGeometry.twistedSheaf M.obj family v
  have hN : N.IsCoherent := AlgebraicGeometry.twistedSheaf_isCoherent M.obj family v
  have hv : Function.update v 0 (v 0 + 1) = 0 := by
    funext i
    fin_cases i
    rfl
  let e : M.obj ≅ (tensorFunctor X L).obj N :=
    (AlgebraicGeometry.twistedSheafZeroIso M.obj family).symm ≪≫
      eqToIso (congrArg (AlgebraicGeometry.twistedSheaf M.obj family) hv.symm) ≪≫
        AlgebraicGeometry.twistedSheafUpdateIso M.obj family v 0
  exact ⟨⟨N, hN⟩, ⟨ObjectProperty.isoMk _ e.symm⟩⟩

instance functor_isEquivalence : (functor X L).IsEquivalence := { }

/-- The actual tensor functor is an equivalence on Coh(X). -/
def equivalence : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ≌
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf := (functor X L).asEquivalence

#print axioms equivalence

end Beilinson.CoherentTensor

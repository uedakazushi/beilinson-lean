module

public import Beilinson.KroneckerResolution
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.RingTheory.Finiteness.Finsupp

/-! Finite-dimensional Kronecker modules form a Serre subcategory. Its finite
projective covers lift through every epimorphism onto a finite-dimensional object.
These are the inputs for comparing its own bounded derived category with bounded
finite-dimensional cohomology in the ambient module derived category. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Beilinson.Kronecker

universe u v

variable (k : Type u) [Field k]

/-- Finite-dimensional vector spaces, as an object property. -/
def finiteVectorSpaces : ObjectProperty (ModuleCat.{v} k) := fun M => Module.Finite k M

instance finiteVectorSpaces_serre : (finiteVectorSpaces.{u,v} k).IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, by
    let : Subsingleton (0 : ModuleCat.{v} k) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
    dsimp [finiteVectorSpaces]
    infer_instance⟩
  prop_of_mono {X Y} f _ hY := by
    let : Module.Finite k Y := hY
    exact Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)
  prop_of_epi {X Y} f _ hX := by
    let : Module.Finite k X := hX
    exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    let : Module.Finite k S.X₁ := h₁
    let : Module.Finite k S.X₃ := h₃
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
      ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)

/-- Finite-dimensional right modules are stable under subobjects, quotients and extensions. -/
instance finiteRightModules_serre : (finiteRightModules.{u,v} (k := k)).IsSerreClass :=
  inferInstanceAs ((finiteVectorSpaces.{u,v} k).inverseImage
    (ModuleCat.restrictScalars (algebraMap k (Algebra k)ᵐᵒᵖ))).IsSerreClass

/-- A finite projective cover of the target lifts through any epimorphism. -/
theorem finiteRightModules_coversEpis {X Y : ModuleCat.{v} (Algebra k)ᵐᵒᵖ}
    (f : X ⟶ Y) [hf : Epi f] (hY : finiteRightModules Y) :
    ∃ (P : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) (g : P ⟶ X),
      finiteRightModules P ∧ Epi (g ≫ f) := by
  let P := (rightModuleResolution Y).X₂
  let p : P ⟶ Y := (rightModuleResolution Y).g
  let : Epi p := (rightModuleResolution_shortExact Y).epi_g
  refine ⟨P, Projective.factorThru p f,
    (finite_rightModuleResolution_terms Y hY).2, ?_⟩
  exact (Projective.factorThru_comp p f).symm ▸ (inferInstance : Epi p)

end Beilinson.Kronecker

module

public import Beilinson.KroneckerFinite
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! Finite-dimensional modules over any finite-dimensional algebra form a Serre
subcategory whose finite free covers lift through arbitrary epimorphisms. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace Beilinson.FiniteModuleCategory

universe u
variable (k : Type u) [Field k] (S : Type u) [Ring S] [Algebra k S]

/-- Ordinary left S-modules finite over the coefficient field. Use S = Aᵐᵒᵖ for right modules. -/
def finiteModules : ObjectProperty (ModuleCat.{u} S) :=
  (Kronecker.finiteVectorSpaces k).inverseImage
    (ModuleCat.restrictScalars (algebraMap k S))

instance finiteModules_serre : (finiteModules k S).IsSerreClass :=
  inferInstanceAs ((Kronecker.finiteVectorSpaces k).inverseImage
    (ModuleCat.restrictScalars (algebraMap k S))).IsSerreClass

/-- A finite free presentation of the target provides a lift through any epimorphism. -/
theorem coversEpis [Module.Finite k S] {X Y : ModuleCat.{u} S}
    (f : X ⟶ Y) [Epi f] (hY : finiteModules k S Y) :
    ∃ (P : ModuleCat.{u} S) (g : P ⟶ X), finiteModules k S P ∧ Epi (g ≫ f) := by
  let : Module.Finite k Y := hY
  let : Module.Finite S Y := Module.Finite.of_restrictScalars_finite k S Y
  obtain ⟨m, p, hp⟩ := Module.Finite.exists_fin' (R := S) (M := Y)
  let P : ModuleCat.{u} S := ModuleCat.of S (Fin m → S)
  let q : P ⟶ Y := ModuleCat.ofHom p
  let : Epi q := (ModuleCat.epi_iff_surjective q).2 hp
  refine ⟨P, Projective.factorThru q f, ?_, ?_⟩
  · change Module.Finite k ((ModuleCat.restrictScalars (algebraMap k S)).obj P)
    let : Module S ((ModuleCat.restrictScalars (algebraMap k S)).obj P) :=
      inferInstanceAs (Module S (Fin m → S))
    let : Module.Finite S ((ModuleCat.restrictScalars (algebraMap k S)).obj P) :=
      inferInstanceAs (Module.Finite S (Fin m → S))
    let : IsScalarTower k S ((ModuleCat.restrictScalars (algebraMap k S)).obj P) :=
      IsScalarTower.of_compHom k S (Fin m → S)
    exact Module.Finite.trans (R := k) S _
  · exact (Projective.factorThru_comp q f).symm ▸ (inferInstance : Epi q)

end Beilinson.FiniteModuleCategory

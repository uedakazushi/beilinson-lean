module

public import Beilinson.KroneckerEnd
public import Beilinson.KroneckerResolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Transport the explicit length-one resolution to any ring identified with the
Kronecker algebra, in particular the categorical endomorphism algebra of a pair. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Beilinson.KroneckerEndModules

universe u v w t

variable {k : Type u} [Field k] {S : Type v} [Ring S]

/-- Ordinary right modules are transported by the opposite of the ring isomorphism. -/
def rightModules (e : Kronecker.Algebra k ≃+* S) :
    ModuleCat.{t} Sᵐᵒᵖ ≌ ModuleCat.{t} (Kronecker.Algebra k)ᵐᵒᵖ :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.op e)

instance rightModules_additive (e : Kronecker.Algebra k ≃+* S) :
    (rightModules.{u,v,t} e).functor.Additive :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv_additive _

/-- Transport of the two projective terms and their short exact sequence. -/
def resolution (e : Kronecker.Algebra k ≃+* S) (M : ModuleCat.{t} Sᵐᵒᵖ) :
    ShortComplex (ModuleCat.{t} Sᵐᵒᵖ) :=
  (Kronecker.rightModuleResolution ((rightModules e).functor.obj M)).map
    (rightModules e).inverse

theorem resolution_shortExact (e : Kronecker.Algebra k ≃+* S)
    (M : ModuleCat.{t} Sᵐᵒᵖ) : (resolution e M).ShortExact := by
  let E := rightModules e
  let : E.inverse.Additive := inferInstance
  exact (Kronecker.rightModuleResolution_shortExact (E.functor.obj M)).map_of_exact E.inverse

instance resolution_projective₁ (e : Kronecker.Algebra k ≃+* S)
    (M : ModuleCat.{t} Sᵐᵒᵖ) : Projective (resolution e M).X₁ :=
  ((rightModules e).symm.map_projective_iff _).mpr inferInstance

instance resolution_projective₀ (e : Kronecker.Algebra k ≃+* S)
    (M : ModuleCat.{t} Sᵐᵒᵖ) : Projective (resolution e M).X₂ :=
  ((rightModules e).symm.map_projective_iff _).mpr inferInstance

/-- The last term is canonically the original module. -/
def resolutionTargetIso (e : Kronecker.Algebra k ≃+* S)
    (M : ModuleCat.{t} Sᵐᵒᵖ) : (resolution e M).X₃ ≅ M :=
  ((rightModules e).unitIso.app M).symm

/-- The ring identification transfers the uniform projective-dimension bound. -/
theorem projectiveDimension_le_one (e : Kronecker.Algebra k ≃+* S)
    (M : ModuleCat.{t} Sᵐᵒᵖ) : projectiveDimension M ≤ 1 := by
  let : HasProjectiveDimensionLT (resolution e M).X₃ 2 :=
    (resolution_shortExact e M).hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance
  exact (projectiveDimension_le_iff M 1).mpr
    (hasProjectiveDimensionLT_of_iso (resolutionTargetIso e M) 2)

variable (k) {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasBinaryBiproducts C] {X Y : C} [Subsingleton (Y ⟶ X)]

/-- With the explicit Hom hypotheses, every right End(X ⊕ Y)-module has dimension at most one. -/
theorem end_projectiveDimension_le_one
    (e₀ : (X ⟶ X) ≃ₗ[k] k) (e₁ : (Y ⟶ Y) ≃ₗ[k] k)
    (b : Module.Basis (Fin 2) k (X ⟶ Y)) (h₀ : e₀ (𝟙 X) = 1) (h₁ : e₁ (𝟙 Y) = 1)
    (M : ModuleCat.{t} (End (X ⊞ Y))ᵐᵒᵖ) : projectiveDimension M ≤ 1 :=
  projectiveDimension_le_one (KroneckerEnd.algebraEquiv k e₀ e₁ b h₀ h₁).toRingEquiv M

end Beilinson.KroneckerEndModules

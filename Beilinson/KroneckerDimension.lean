module

public import Beilinson.KroneckerResolution
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Sharpness of the right-module projective dimension bound

The representation concentrated at the source vertex has no lift of its identity
along the standard projective augmentation. Hence its associated right module is
not projective and has projective dimension exactly one.
-/

@[expose] public section

open CategoryTheory Module

universe u

namespace Beilinson.Kronecker

variable (k : Type u) [Field k]

/-- The one-dimensional representation concentrated at vertex 1. -/
def sourceSimple : ReverseRep.{u,u} k where
  V₀ := ModuleCat.of k PUnit.{u+1}
  V₁ := ModuleCat.of k k
  arrow := fun _ => 0

/-- The standard augmentation onto the source representation is an epimorphism. -/
instance sourceSimple_augment_epi : Epi (ReverseRep.augment (sourceSimple k)) := by
  apply (ReverseRep.epi_iff_surjective _).mpr
  constructor
  · intro m
    refine ⟨(m, (0, 0)), ?_⟩
    change m + 0 + 0 = m
    simp
  · exact Function.surjective_id

/-- No section of the augmentation can commute with the first arrow. -/
theorem sourceSimple_not_projective : ¬ Projective (sourceSimple k) := by
  intro h
  let := h
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 (sourceSimple k))
    (ReverseRep.augment (sourceSimple k))
  have h₁ := LinearMap.congr_fun (congrArg ReverseRep.Hom.one hs) (1 : k)
  change s.one (1 : k) = (1 : k) at h₁
  have hc := LinearMap.congr_fun (s.comm 0) (1 : k)
  change s.zero 0 = (0, (s.one (1 : k), 0)) at hc
  rw [map_zero] at hc
  have hz := congrArg (fun m => m.2.1) hc
  change (0 : k) = s.one (1 : k) at hz
  exact zero_ne_one (hz.trans h₁)

/-- The right module corresponding to the source representation. -/
def sourceSimpleModule : ModuleCat.{u} (Algebra k)ᵐᵒᵖ :=
  fromReverseRep.obj (sourceSimple k)

/-- The source module is simple: every nonzero vector generates it. -/
theorem sourceSimpleModule_simple : IsSimpleModule (Algebra k)ᵐᵒᵖ (sourceSimpleModule k) := by
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  constructor
  · change Nontrivial (PUnit.{u+1} × k)
    infer_instance
  · intro m hm n
    let m₂ : k := m.2
    let n₂ : k := n.2
    have hm₂ : m.2 ≠ (0 : k) := by
      intro hz
      apply hm
      apply Prod.ext
      · exact Subsingleton.elim (α := PUnit.{u+1}) _ _
      · exact hz
    refine ⟨MulOpposite.op (coordinates k ![0, n₂ / m₂, 0, 0]), ?_⟩
    change actionOfArrows (sourceSimple k).arrow
      (coordinates k ![0, n₂ / m₂, 0, 0]) m = n
    apply (actionOfArrows_coordinates (sourceSimple k).arrow ![0, n₂ / m₂, 0, 0] m).trans
    change (PUnit.unit, n₂ / m₂ * m₂) = n
    apply Prod.ext
    · exact Subsingleton.elim (α := PUnit.{u+1}) _ _
    · exact div_mul_cancel₀ _ hm₂

/-- Non-projectivity survives the category equivalence. -/
theorem sourceSimpleModule_not_projective : ¬ Projective (sourceSimpleModule k) := by
  intro h
  exact sourceSimple_not_projective k
    ((moduleEquivalence.symm.map_projective_iff (sourceSimple k)).mp h)

/-- The universal bound one is attained by the source representation. -/
theorem sourceSimpleModule_projectiveDimension : projectiveDimension (sourceSimpleModule k) = 1 := by
  apply le_antisymm (rightModule_projectiveDimension_le_one _)
  apply (projectiveDimension_ge_iff (sourceSimpleModule k) 1).mpr
  intro h
  exact sourceSimpleModule_not_projective k
    (projective_iff_hasProjectiveDimensionLT_one.mpr h)

/-- The example attaining the bound is finite dimensional over the ground field. -/
theorem sourceSimpleModule_finite : finiteRightModules (sourceSimpleModule k) := by
  apply (finite_fromReverseRep_iff (sourceSimple k)).mpr
  constructor
  · change FiniteDimensional k PUnit.{u+1}
    infer_instance
  · change FiniteDimensional k k
    infer_instance

end Beilinson.Kronecker

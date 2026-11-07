module

public import Beilinson.KroneckerCategory
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# The standard length-one projective presentation

For a reverse Kronecker representation X, use the cover with vertex spaces
`X₀ × (X₁ × X₁)` and `X₁`. The two arrows insert into the two copies of `X₁`.
Its kernel is the sink representation on `X₁ × X₁`.
-/

@[expose] public section

open CategoryTheory Module CategoryTheory.Limits

universe u v

namespace Beilinson.Kronecker

variable {k : Type u} [Field k]

local instance : (fromReverseRep (k := k)).IsEquivalence :=
  (moduleEquivalence (k := k)).isEquivalence_inverse

namespace ReverseRep

/-- Epimorphisms are exactly the maps surjective at both vertices. -/
theorem epi_iff_surjective {X Y : ReverseRep.{u,v} k} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f.zero ∧ Function.Surjective f.one := by
  rw [← fromReverseRep.epi_map_iff_epi, ModuleCat.epi_iff_surjective]
  constructor
  · intro h
    constructor
    · intro y
      obtain ⟨x, hx⟩ := h (y, 0)
      exact ⟨x.1, congrArg Prod.fst hx⟩
    · intro y
      obtain ⟨x, hx⟩ := h (0, y)
      exact ⟨x.2, congrArg Prod.snd hx⟩
  · rintro ⟨h₀, h₁⟩ ⟨y₀, y₁⟩
    obtain ⟨x₀, rfl⟩ := h₀ y₀
    obtain ⟨x₁, rfl⟩ := h₁ y₁
    exact ⟨(x₀, x₁), rfl⟩

/-- The projective representation concentrated at the sink, with coefficient space V. -/
def sink (V : ModuleCat.{v} k) : ReverseRep.{u,v} k where
  V₀ := V
  V₁ := ModuleCat.of k PUnit.{v+1}
  arrow := fun _ => 0

/-- The standard projective presentation object, before specifying its augmentation. -/
def cover (X : ReverseRep.{u,v} k) : ReverseRep.{u,v} k where
  V₀ := ModuleCat.of k (X.V₀ × (X.V₁ × X.V₁))
  V₁ := X.V₁
  arrow i := if i = 0 then
    (LinearMap.inr k X.V₀ (X.V₁ × X.V₁)).comp (LinearMap.inl k X.V₁ X.V₁)
    else (LinearMap.inr k X.V₀ (X.V₁ × X.V₁)).comp (LinearMap.inr k X.V₁ X.V₁)

/-- The cover maps onto X by evaluation of the two arrow coefficients. -/
def augment (X : ReverseRep.{u,v} k) : cover X ⟶ X where
  zero := LinearMap.fst k X.V₀ (X.V₁ × X.V₁) +
    (X.arrow 0).comp ((LinearMap.fst k X.V₁ X.V₁).comp (LinearMap.snd k X.V₀ _)) +
    (X.arrow 1).comp ((LinearMap.snd k X.V₁ X.V₁).comp (LinearMap.snd k X.V₀ _))
  one := LinearMap.id
  comm i := by
    fin_cases i
    · ext m
      change 0 + X.arrow 0 m + X.arrow 1 0 = X.arrow 0 m
      simp
    · ext m
      change 0 + X.arrow 0 0 + X.arrow 1 m = X.arrow 1 m
      simp

/-- The relation term sits at the sink only. -/
def relations (X : ReverseRep.{u,v} k) : ReverseRep.{u,v} k :=
  sink (ModuleCat.of k (X.V₁ × X.V₁))

/-- Include the two arrow relations into the cover. -/
def relationMap (X : ReverseRep.{u,v} k) : relations X ⟶ cover X where
  zero := (-(X.arrow 0).comp (LinearMap.fst k X.V₁ X.V₁) -
    (X.arrow 1).comp (LinearMap.snd k X.V₁ X.V₁)).prod LinearMap.id
  one := 0
  comm i := by
    ext m
    change (-X.arrow 0 0 - X.arrow 1 0, (0, 0)) = (cover X).arrow i 0
    simp only [map_zero]
    change (- (0 : X.V₀) - 0, (0, 0)) = (0, (0, 0))
    simp

/-- Sink representations are projective because vector spaces lift along surjections. -/
instance projective_sink (V : ModuleCat.{v} k) : Projective (sink V) where
  factors {E Y} f e he := by
    obtain ⟨l, hl⟩ := Module.projective_lifting_property e.zero f.zero
      ((epi_iff_surjective e).mp he).1
    refine ⟨{ zero := l, one := 0, comm := ?_ }, ?_⟩
    · intro i
      ext m
      change l 0 = E.arrow i 0
      simp
    · apply hom_ext
      · exact hl
      · ext m
        have hm : m = 0 := by cases m; rfl
        rw [hm]
        simp

/-- The standard cover is projective, without a finite-dimensionality assumption. -/
instance projective_cover (X : ReverseRep.{u,v} k) : Projective (cover X) where
  factors {E Y} f e he := by
    obtain ⟨l₀, h₀⟩ := Module.projective_lifting_property e.zero
      (f.zero.comp (LinearMap.inl k X.V₀ (X.V₁ × X.V₁)))
      ((epi_iff_surjective e).mp he).1
    obtain ⟨l₁, h₁⟩ := Module.projective_lifting_property e.one f.one
      ((epi_iff_surjective e).mp he).2
    let l : cover X ⟶ E :=
      { zero := l₀.comp (LinearMap.fst k X.V₀ _) +
          (E.arrow 0).comp (l₁.comp ((LinearMap.fst k X.V₁ X.V₁).comp (LinearMap.snd k X.V₀ _))) +
          (E.arrow 1).comp (l₁.comp ((LinearMap.snd k X.V₁ X.V₁).comp (LinearMap.snd k X.V₀ _)))
        one := l₁
        comm i := by
          fin_cases i
          · ext m
            change l₀ 0 + E.arrow 0 (l₁ m) + E.arrow 1 (l₁ 0) = E.arrow 0 (l₁ m)
            simp
          · ext m
            change l₀ 0 + E.arrow 0 (l₁ 0) + E.arrow 1 (l₁ m) = E.arrow 1 (l₁ m)
            simp }
    refine ⟨l, ?_⟩
    apply hom_ext
    · ext m
      have h₀m := LinearMap.congr_fun h₀ m.1
      have h₁s := LinearMap.congr_fun h₁ m.2.1
      have h₁t := LinearMap.congr_fun h₁ m.2.2
      have he₀ := LinearMap.congr_fun (e.comm 0) (l₁ m.2.1)
      have he₁ := LinearMap.congr_fun (e.comm 1) (l₁ m.2.2)
      have hf₀ := LinearMap.congr_fun (f.comm 0) m.2.1
      have hf₁ := LinearMap.congr_fun (f.comm 1) m.2.2
      change e.zero (l₀ m.1) = f.zero (m.1, (0, 0)) at h₀m
      change e.one (l₁ m.2.1) = f.one m.2.1 at h₁s
      change e.one (l₁ m.2.2) = f.one m.2.2 at h₁t
      change e.zero (E.arrow 0 (l₁ m.2.1)) = Y.arrow 0 (e.one (l₁ m.2.1)) at he₀
      change e.zero (E.arrow 1 (l₁ m.2.2)) = Y.arrow 1 (e.one (l₁ m.2.2)) at he₁
      change f.zero (0, (m.2.1, 0)) = Y.arrow 0 (f.one m.2.1) at hf₀
      change f.zero (0, (0, m.2.2)) = Y.arrow 1 (f.one m.2.2) at hf₁
      change e.zero (l₀ m.1 + E.arrow 0 (l₁ m.2.1) + E.arrow 1 (l₁ m.2.2)) = f.zero m
      rw [map_add, map_add, h₀m, he₀, he₁, h₁s, h₁t, ← hf₀, ← hf₁]
      let F : (X.V₀ × (X.V₁ × X.V₁)) →ₗ[k] Y.V₀ := f.zero
      change F (m.1, (0, 0)) + F (0, (m.2.1, 0)) + F (0, (0, m.2.2)) = F m
      rw [← map_add, ← map_add]
      congr 1
      ext <;> simp
    · exact h₁

end ReverseRep

/-- The standard presentation as a short complex in mathlib's module category. -/
def standardResolution (X : ReverseRep.{u,v} k) :
    ShortComplex (ModuleCat.{v} (Algebra k)ᵐᵒᵖ) where
  X₁ := fromReverseRep.obj (ReverseRep.relations X)
  X₂ := fromReverseRep.obj (ReverseRep.cover X)
  X₃ := fromReverseRep.obj X
  f := fromReverseRep.map (ReverseRep.relationMap X)
  g := fromReverseRep.map (ReverseRep.augment X)
  zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change ((-X.arrow 0 m.1.1 - X.arrow 1 m.1.2) +
      X.arrow 0 m.1.1 + X.arrow 1 m.1.2, (0 : X.V₁)) = (0, 0)
    apply Prod.ext
    · dsimp
      abel
    · rfl

/-- The relation map is injective. -/
theorem standardResolution_injective (X : ReverseRep.{u,v} k) :
    Function.Injective (standardResolution X).f := by
  intro a b h
  have hab := congrArg (fun m => m.1.2) h
  change a.1 = b.1 at hab
  apply Prod.ext
  · exact hab
  · exact Subsingleton.elim (α := PUnit.{v+1}) a.2 b.2

/-- The augmentation is surjective. -/
theorem standardResolution_surjective (X : ReverseRep.{u,v} k) :
    Function.Surjective (standardResolution X).g := by
  rintro ⟨u, v⟩
  refine ⟨((u, (0, 0)), v), ?_⟩
  change (u + X.arrow 0 0 + X.arrow 1 0, v) = (u, v)
  simp

/-- Exactness identifies the kernel with the two arrow-relation coefficients. -/
theorem standardResolution_exact (X : ReverseRep.{u,v} k) :
    Function.Exact (standardResolution X).f (standardResolution X).g := by
  intro m
  constructor
  · intro h
    have h₀ := congrArg Prod.fst h
    have h₁ := congrArg Prod.snd h
    change m.1.1 + X.arrow 0 m.1.2.1 + X.arrow 1 m.1.2.2 = 0 at h₀
    change m.2 = 0 at h₁
    refine ⟨(m.1.2, PUnit.unit), ?_⟩
    change ((-X.arrow 0 m.1.2.1 - X.arrow 1 m.1.2.2, m.1.2), 0) = m
    apply Prod.ext
    · apply Prod.ext
      · dsimp
        have hz : m.1.1 + (X.arrow 0 m.1.2.1 + X.arrow 1 m.1.2.2) = 0 := by
          simpa only [add_assoc] using h₀
        simpa [sub_eq_add_neg, add_comm] using (eq_neg_of_add_eq_zero_left hz).symm
      · rfl
    · exact h₁.symm
  · rintro ⟨a, rfl⟩
    change ((-X.arrow 0 a.1.1 - X.arrow 1 a.1.2) +
      X.arrow 0 a.1.1 + X.arrow 1 a.1.2, (0 : X.V₁)) = (0, 0)
    apply Prod.ext
    · dsimp
      abel
    · rfl

/-- The standard presentation is short exact. -/
theorem standardResolution_shortExact (X : ReverseRep.{u,v} k) :
    (standardResolution X).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (standardResolution_exact X)
    (standardResolution_injective X) (standardResolution_surjective X)

/-- The relation term is projective. -/
instance standardResolution_projective₁ (X : ReverseRep.{u,v} k) :
    Projective (standardResolution X).X₁ :=
  (moduleEquivalence.symm.map_projective_iff (ReverseRep.relations X)).mpr
    (ReverseRep.projective_sink _)

/-- The cover term is projective. -/
instance standardResolution_projective₀ (X : ReverseRep.{u,v} k) :
    Projective (standardResolution X).X₂ :=
  (moduleEquivalence.symm.map_projective_iff (ReverseRep.cover X)).mpr inferInstance

/-- A length-one projective resolution ending in any given right module. -/
def rightModuleResolution (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :
    ShortComplex (ModuleCat.{v} (Algebra k)ᵐᵒᵖ) where
  X₁ := (standardResolution (toReverseRep.obj M)).X₁
  X₂ := (standardResolution (toReverseRep.obj M)).X₂
  X₃ := M
  f := (standardResolution (toReverseRep.obj M)).f
  g := (standardResolution (toReverseRep.obj M)).g ≫ (moduleUnitIso.app M).inv
  zero := by
    let S := standardResolution (toReverseRep.obj M)
    exact (Category.assoc S.f S.g (moduleUnitIso.app M).inv).symm.trans
      ((congrArg (fun t : S.X₁ ⟶ S.X₃ => t ≫ (moduleUnitIso.app M).inv) S.zero).trans
        (zero_comp))

/-- The terminal change of coordinates from a representation back to its module. -/
def rightModuleResolutionIso (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :
    standardResolution (toReverseRep.obj M) ≅ rightModuleResolution M :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (moduleUnitIso.app M).symm
    (by
      change 𝟙 _ ≫ (standardResolution (toReverseRep.obj M)).f =
        (standardResolution (toReverseRep.obj M)).f ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id])
    (by
      change 𝟙 _ ≫ ((standardResolution (toReverseRep.obj M)).g ≫ (moduleUnitIso.app M).inv) = _
      exact Category.id_comp _)

/-- Every right module has a short exact length-one projective presentation. -/
theorem rightModuleResolution_shortExact (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :
    (rightModuleResolution M).ShortExact :=
  ShortComplex.shortExact_of_iso (rightModuleResolutionIso M)
    (standardResolution_shortExact (toReverseRep.obj M))

instance rightModuleResolution_projective₁ (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :
    Projective (rightModuleResolution M).X₁ :=
  standardResolution_projective₁ (toReverseRep.obj M)

instance rightModuleResolution_projective₀ (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :
    Projective (rightModuleResolution M).X₂ :=
  standardResolution_projective₀ (toReverseRep.obj M)

/-- The inverse equivalence also preserves the finite-dimensional object property. -/
theorem finite_fromReverseRep_iff (X : ReverseRep.{u,v} k) :
    finiteRightModules (fromReverseRep.obj X) ↔ finiteReverseReps X :=
  (finite_toReverseRep_iff _).symm.trans
    ((finiteReverseReps (k := k)).prop_iff_of_iso (representationCounit X))

/-- Finite representations have finite cover and relation terms. -/
theorem finite_resolution_terms (X : ReverseRep.{u,v} k) (hX : finiteReverseReps X) :
    finiteRightModules (standardResolution X).X₁ ∧
      finiteRightModules (standardResolution X).X₂ := by
  let : FiniteDimensional k X.V₀ := hX.1
  let : FiniteDimensional k X.V₁ := hX.2
  constructor
  · apply (finite_fromReverseRep_iff (ReverseRep.relations X)).mpr
    constructor
    · change FiniteDimensional k (X.V₁ × X.V₁)
      infer_instance
    · change FiniteDimensional k PUnit.{v+1}
      infer_instance
  · apply (finite_fromReverseRep_iff (ReverseRep.cover X)).mpr
    constructor
    · change FiniteDimensional k (X.V₀ × (X.V₁ × X.V₁))
      infer_instance
    · exact hX.2

/-- The resolution of a finite-dimensional right module stays finite dimensional. -/
theorem finite_rightModuleResolution_terms (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ)
    (hM : finiteRightModules M) :
    finiteRightModules (rightModuleResolution M).X₁ ∧
      finiteRightModules (rightModuleResolution M).X₂ :=
  finite_resolution_terms (toReverseRep.obj M) ((finite_toReverseRep_iff M).mpr hM)

/-- Every right module over the concrete Kronecker algebra has projective dimension at most one. -/
theorem rightModule_projectiveDimension_le_one (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :
    projectiveDimension M ≤ 1 := by
  apply (projectiveDimension_le_iff M 1).mpr
  exact (rightModuleResolution_shortExact M).hasProjectiveDimensionLT_X₃ 1
    inferInstance inferInstance

end Beilinson.Kronecker

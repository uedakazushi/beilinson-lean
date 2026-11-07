module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! A bounded derived object lies in any strictly full triangulated subcategory
containing its cohomology objects in degree zero. This works for every abelian
category, including modules over a noncommutative ring. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Beilinson.DerivedDevissage

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem homology_mor₁_isIso (T : Pretriangulated.Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (i : ℤ)
    (hPrev : IsZero ((DerivedCategory.homologyFunctor C (i - 1)).obj T.obj₃))
    (hNow : IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
    have hS := DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega)
    have hz : DerivedCategory.HomologySequence.δ T (i - 1) i (by omega) = 0 :=
      hPrev.eq_of_src _ _
    exact hS.mono_g hz
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
    have hS := DerivedCategory.HomologySequence.exact₂ T hT i
    have hz : (DerivedCategory.homologyFunctor C i).map T.mor₂ = 0 := hNow.eq_of_tgt _ _
    exact hS.epi_f hz
  exact isIso_of_mono_of_epi _

private theorem homology_mor₂_isIso (T : Pretriangulated.Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (i : ℤ)
    (hNow : IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₁))
    (hNext : IsZero ((DerivedCategory.homologyFunctor C (i + 1)).obj T.obj₁)) :
    IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
    have hS := DerivedCategory.HomologySequence.exact₂ T hT i
    have hz : (DerivedCategory.homologyFunctor C i).map T.mor₁ = 0 := hNow.eq_of_src _ _
    exact hS.mono_g hz
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
    have hS := DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl
    have hz : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := hNext.eq_of_tgt _ _
    exact hS.epi_f hz
  exact isIso_of_mono_of_epi _

variable (P : ObjectProperty (DerivedCategory C))
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

private theorem concentrated (K : DerivedCategory C) (a : ℤ) [K.IsGE a] [K.IsLE a]
    (h : P ((DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C a).obj K))) : P K := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K a
  let eM := (DerivedCategory.homologyFunctor C a).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C a).app M
  have hM : P ((DerivedCategory.singleFunctor C 0).obj M) :=
    P.prop_of_iso ((DerivedCategory.singleFunctor C 0).mapIso eM) h
  let eShift := ((DerivedCategory.singleFunctors C).shiftIso (-a) a 0 (by omega)).app M
  exact P.prop_of_iso e.symm (P.prop_of_iso eShift (P.le_shift (-a) _ hM))

/-- Bounded objects can be assembled from their cohomology objects by finitely
many shifts and distinguished triangles. No commutativity or projectivity is assumed. -/
theorem of_bounded_cohomology (K : DerivedCategory C) (a b : ℤ)
    [K.IsGE a] [K.IsLE b] (hab : a ≤ b)
    (hH : ∀ i : ℤ, P ((DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C i).obj K))) : P K := by
  let H := DerivedCategory.homologyFunctor C
  let S := DerivedCategory.singleFunctor C 0
  suffices h : ∀ d : ℕ, ∀ (K : DerivedCategory C) (a b : ℤ),
      [K.IsGE a] → [K.IsLE b] → a ≤ b → b - a = (d : ℤ) →
      (∀ i : ℤ, P (S.obj ((H i).obj K))) → P K from
    h (Int.toNat (b - a)) K a b hab (by omega) hH
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro K a b hGE hLE hab hd hH
    by_cases hab' : a = b
    · subst b
      exact concentrated P K a (hH a)
    · have hab'' : a < b := lt_of_le_of_ne hab hab'
      let t := DerivedCategory.TStructure.t (C := C)
      let T := (t.triangleLEGE (b - 1) b (by omega)).obj K
      have hT : T ∈ distTriang (DerivedCategory C) :=
        t.triangleLEGE_distinguished (b - 1) b (by omega) K
      have : T.obj₁.IsGE a := by
        change ((t.truncLE (b - 1)).obj K).IsGE a
        infer_instance
      have : T.obj₁.IsLE (b - 1) := by
        change ((t.truncLE (b - 1)).obj K).IsLE (b - 1)
        infer_instance
      have : T.obj₃.IsGE b := by
        change ((t.truncGE b).obj K).IsGE b
        infer_instance
      have : T.obj₃.IsLE b := by
        change ((t.truncGE b).obj K).IsLE b
        infer_instance
      have : IsIso ((H b).map T.mor₂) := homology_mor₂_isIso T hT b
        (DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) b (by omega))
        (DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) (b + 1) (by omega))
      have h₃ : P T.obj₃ := concentrated P T.obj₃ b
        (P.prop_of_iso (S.mapIso (asIso ((H b).map T.mor₂))) (hH b))
      have h₁H (i : ℤ) : P (S.obj ((H i).obj T.obj₁)) := by
        by_cases hi : i ≤ b - 1
        · have : IsIso ((H i).map T.mor₁) := homology_mor₁_isIso T hT i
            (DerivedCategory.isZero_of_isGE T.obj₃ b (i - 1) (by omega))
            (DerivedCategory.isZero_of_isGE T.obj₃ b i (by omega))
          exact P.prop_of_iso (S.mapIso (asIso ((H i).map T.mor₁))).symm (hH i)
        · exact P.prop_of_isZero (S.map_isZero
            (DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) i (by omega)))
      have h₁ : P T.obj₁ := ih (d - 1) (by omega) T.obj₁ a (b - 1)
        (by omega) (by omega) h₁H
      exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

/-- The same criterion with existential cohomological bounds. -/
theorem of_isBounded (K : DerivedCategory C)
    (hK : (∃ a : ℤ, K.IsGE a) ∧ ∃ b : ℤ, K.IsLE b)
    (hH : ∀ i : ℤ, P ((DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C i).obj K))) : P K := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK
  let := ha
  let := hb
  let : K.IsLE (max a b) :=
    DerivedCategory.TStructure.t.isLE_of_le K b (max a b) (le_max_right _ _)
  exact of_bounded_cohomology P K a (max a b) (le_max_left _ _) hH

end Beilinson.DerivedDevissage

module

public import StacksFrontier.CategoryTheory.Triangulated.ExceptionalCollectionFiniteness

/-!
# An audited abstract generation criterion

This focused optional probe imports one Stacks module, whose own imports are all
from mathlib. It does not import the Stacks umbrella or assert the geometric
hypotheses for projective space. The upstream revision is pinned in the manifest.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Beilinson.StacksProbe

universe w v u

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Preadditive C]
  [HasShift C ℤ] [Linear k C]

section Generation
variable [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- An exceptional collection which detects zero and has finite total Hom
is contained in no proper strictly full triangulated subcategory. -/
theorem full_of_exceptional_and_detection {r : ℕ} (G : Fin r → C)
    (hscalar : ∀ a (f : G a ⟶ G a), ∃ c : k, f = c • 𝟙 (G a))
    (hself : ∀ a (n : ℤ), n ≠ 0 → Subsingleton (G a ⟶ (G a)⟦n⟧))
    (hsemi : ∀ a b : Fin r, a < b → ∀ n : ℤ, Subsingleton (G b ⟶ (G a)⟦n⟧))
    (hfinite : ∀ a (M : C), HasFiniteTotalHom k (G a) M)
    (hdetect : ∀ M : C, (∀ a (n : ℤ), Subsingleton (G a ⟶ M⟦n⟧)) → IsZero M)
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ a, P (G a)) : P = ⊤ := by
  let : (⊤ : ObjectProperty C).IsTriangulated :=
    { ext₂' T _ _ _ := ⟨T.obj₂, trivial, ⟨Iso.refl _⟩⟩ }
  apply top_unique
  intro M _
  exact prop_of_hasFiniteTotalHom_of_exceptional k G hscalar hself hsemi
    (fun a b _ => hfinite a (G b)) ⊤ (fun _ => trivial)
    (fun M _ h => hdetect M h) P hP M trivial (fun a => hfinite a M)

end Generation

/-- Finite total Hom descends to every retract of the source object. -/
theorem finiteTotalHom_retract {E G M : C} (i : G ⟶ E) (p : E ⟶ G)
    (hip : i ≫ p = 𝟙 G) (h : HasFiniteTotalHom k E M) : HasFiniteTotalHom k G M := by
  have hinj (n : ℤ) : Function.Injective
      (Linear.leftComp k (M⟦n⟧) p) := by
    intro f g hfg
    have hh := congrArg (fun t => i ≫ t) hfg
    simpa only [Linear.leftComp_apply, ← Category.assoc, hip, Category.id_comp] using hh
  constructor
  · intro n
    let := h.1 n
    exact Module.Finite.of_injective (Linear.leftComp k (M⟦n⟧) p) (hinj n)
  · apply h.2.subset
    intro n hn
    let : Nontrivial (G ⟶ M⟦n⟧) := hn
    exact (hinj n).nontrivial

section Transport
universe v' u'
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ] [Linear k D]

/-- A fully faithful coefficient-linear functor commuting with shifts preserves and
reflects finite total Hom; an integral linearity statement would not suffice. -/
theorem finiteTotalHom_iff_map (F : C ⥤ D) [F.Additive] [F.Linear k]
    [F.Full] [F.Faithful] [F.CommShift ℤ] (X M : C) :
    HasFiniteTotalHom k X M ↔ HasFiniteTotalHom k (F.obj X) (F.obj M) := by
  let e (n : ℤ) : (X ⟶ M⟦n⟧) ≃ₗ[k] (F.obj X ⟶ (F.obj M)⟦n⟧) :=
    (LinearEquiv.ofBijective (F.mapLinearMap k)
      ⟨F.map_injective, F.map_surjective⟩) ≪≫ₗ
        Linear.homCongr k (Iso.refl _) ((F.commShiftIso n).app M)
  have hs : {n : ℤ | Nontrivial (X ⟶ M⟦n⟧)} =
      {n : ℤ | Nontrivial (F.obj X ⟶ (F.obj M)⟦n⟧)} := by
    ext n
    exact (e n).nontrivial_congr
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨fun n => ?_, hs ▸ hb⟩
    let := hf n
    exact Module.Finite.equiv (e n)
  · rintro ⟨hf, hb⟩
    refine ⟨fun n => ?_, hs.symm ▸ hb⟩
    let := hf n
    exact Module.Finite.equiv (e n).symm

end Transport

#print axioms Beilinson.StacksProbe.finiteTotalHom_iff_map
#print axioms Beilinson.StacksProbe.finiteTotalHom_retract
#print axioms CategoryTheory.Pretriangulated.prop_of_hasFiniteTotalHom_of_exceptional
#print axioms Beilinson.StacksProbe.full_of_exceptional_and_detection

end Beilinson.StacksProbe

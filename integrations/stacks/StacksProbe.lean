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
  [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Linear k C] [∀ n : ℤ, (shiftFunctor C n).Linear k]

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

#print axioms CategoryTheory.Pretriangulated.prop_of_hasFiniteTotalHom_of_exceptional
#print axioms Beilinson.StacksProbe.full_of_exceptional_and_detection

end Beilinson.StacksProbe

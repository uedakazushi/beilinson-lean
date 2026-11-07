module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul

/-! The finite Beilinson window controls all non-positive twists by coordinate
Koszul descent. No diagonal resolution or geometric zero-detection is assumed here. -/

attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ExampleGenerator Stacks.TriangulatedGenerators

namespace Beilinson.StacksGenerationProbe

universe u

variable (A : Type u) [CommRing A] (n : ℕ)

/-- All negative twists belong to the thick subcategory of the finite twist sum. -/
theorem negative_twist_generated (m : ℕ) :
    twist A n (-(m : ℤ)) ∈ gen (twistSum A n) :=
  twist_neg_mem_gen A n m

/-- Orthogonality to the finite twist sum propagates to all non-positive twists. -/
theorem negative_twist_orthogonal (K : DerivedCategory (Mods A n))
    (h : ∀ (j : ℤ) (f : twistSum A n ⟶ K⟦j⟧), f = 0)
    (m : ℕ) (q : ℤ) (f : (twist A n (-(m : ℤ)))⟦q⟧ ⟶ K) : f = 0 :=
  (hom_vanishing_iff_gen (twistSum A n) K).1 h _
    (shift_mem_gen_of_mem q (negative_twist_generated A n m)) f

#print axioms Beilinson.StacksGenerationProbe.negative_twist_generated
#print axioms Beilinson.StacksGenerationProbe.negative_twist_orthogonal

end Beilinson.StacksGenerationProbe

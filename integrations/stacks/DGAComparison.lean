module

public import StacksFrontier.Algebra.DifferentialGraded.AlgebraCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra

/-! Lift an ordinary algebra identification to a strict dg algebra identification.
The geometric endomorphism algebra exposes the concentration and differential
hypotheses separately; a ring equivalence alone does not supply this dg adapter. -/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedAlgebra

namespace Beilinson.DGAComparison

universe u

variable {R : Type u} [CommRing R] (B : DifferentialGradedAlgebra.{u, u} R)
  {S : Type u} [Ring S] [Algebra R S]

/-- A concentrated dg algebra with an identified ordinary algebra is strictly
isomorphic to that algebra in degree zero. -/
def degreeZeroIso (e : B.A ≃ₐ[R] S)
    (hzero : ∀ x : B.A, x ∈ B.grading 0)
    (hbot : ∀ n : ℤ, n ≠ 0 → B.grading n = ⊥)
    (hd : ∀ x : B.A, B.d x = 0) : B ≅ degreeZero R S where
  hom :=
    { toAlgebraHom := e.toAlgHom
      map_grading := by
        intro n a ha
        by_cases hn : n = 0
        · subst n
          simp [degreeZero, degreeZeroGrading]
        · have ha0 : a = 0 := by simpa [hbot n hn] using ha
          simp [ha0, degreeZero, degreeZeroGrading, hn]
      map_d := by
        intro a
        change e (B.d a) = 0
        rw [hd, map_zero] }
  inv :=
    { toAlgebraHom := e.symm.toAlgHom
      map_grading := by
        intro n a ha
        change e.symm a ∈ B.grading n
        by_cases hn : n = 0
        · subst n
          exact hzero _
        · have ha0 : a = 0 := by
            simpa [degreeZero, degreeZeroGrading, hn] using ha
          simp [ha0]
      map_d := by
        intro a
        change e.symm 0 = B.d (e.symm a)
        rw [map_zero, hd] }
  hom_inv_id := by
    apply hom_eq_of_toAlgebraHom_eq
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply hom_eq_of_toAlgebraHom_eq
    ext x
    exact e.apply_symm_apply x

#print axioms Beilinson.DGAComparison.degreeZeroIso

end Beilinson.DGAComparison

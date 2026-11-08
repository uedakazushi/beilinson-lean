module

public import DGAComparison
public import DegreeZeroConeComparison
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! A dg algebra with the literal same underlying algebra, concentrated in degree
zero, equals its standard degree-zero presentation. This permits transport of
its cone-model derived category without a change-of-algebra Morita theorem. -/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedAlgebra DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

namespace Beilinson.ConcentratedDGA

universe u

variable {R : Type u} [CommRing R]

theorem gradedAlgebra_unique {A : Type u} [Ring A] [Algebra R A]
    (g : ℤ → Submodule R A) (p q : GradedAlgebra g) : p = q := by
  have h : p.toDecomposition = q.toDecomposition := Subsingleton.elim _ _
  cases p
  cases q
  cases h
  rfl

/-- A concentrated dg algebra is its degree-zero model when the underlying algebra is retained. -/
theorem eq_degreeZero_self (B : DifferentialGradedAlgebra.{u, u} R)
    (hzero : ∀ x : B.A, x ∈ B.grading 0)
    (hbot : ∀ n : ℤ, n ≠ 0 → B.grading n = ⊥)
    (hd : ∀ x : B.A, B.d x = 0) : B = degreeZero R B.A := by
  have hg : B.grading = degreeZeroGrading R B.A := by
    funext n
    by_cases hn : n = 0
    · subst n
      rw [degreeZeroGrading_zero]
      exact Submodule.eq_top_iff'.2 hzero
    · rw [degreeZeroGrading_eq_bot R B.A hn]
      exact hbot n hn
  have hd0 : B.d = 0 := LinearMap.ext hd
  cases B with
  | mk A grading d hdd hmem hleibniz =>
    change grading = degreeZeroGrading R A at hg
    change d = (0 : A →ₗ[R] A) at hd0
    clear hzero hbot hd
    subst grading
    subst d
    congr 1
    exact gradedAlgebra_unique _ _ _

/-- An equivalence to ordinary right modules, together with its exact shift structure. -/
structure Comparison (B : DifferentialGradedAlgebra.{u, u} R) where
  equivalence : derivedCategory.{u, u, u} B ≌ DerivedCategory (ModuleCat.{u} B.Aᵐᵒᵖ)
  commShift : equivalence.functor.CommShift ℤ
  isTriangulated : letI := commShift; equivalence.functor.IsTriangulated

/-- The standard comparison, with the sign correction required by the cone convention. -/
def standardComparison (R : Type u) [CommRing R] (S : Type u) [Ring S] [Algebra R S] :
    Comparison (degreeZero R S) :=
  { equivalence := DegreeZeroConeComparison.coneRightModuleComparison R S
    commShift := Classical.choose (DegreeZeroConeComparison.coneRightModuleComparison_exact R S)
    isTriangulated := Classical.choose_spec
      (DegreeZeroConeComparison.coneRightModuleComparison_exact R S) }

/-- A concentrated dg algebra has the triangulated derived category of its ordinary right modules. -/
def comparison (B : DifferentialGradedAlgebra.{u, u} R)
    (hzero : ∀ x : B.A, x ∈ B.grading 0)
    (hbot : ∀ n : ℤ, n ≠ 0 → B.grading n = ⊥)
    (hd : ∀ x : B.A, B.d x = 0) : Comparison B :=
  (eq_degreeZero_self B hzero hbot hd).symm ▸ standardComparison R B.A

namespace Comparison

variable {B : DifferentialGradedAlgebra.{u, u} R} (c : Comparison B)

/-- The canonical compatible shift structure on the inverse equivalence. -/
@[instance_reducible]
def inverseCommShift : c.equivalence.inverse.CommShift ℤ :=
  letI := c.commShift
  c.equivalence.commShiftInverse ℤ

/-- The inverse comparison is exact as well. -/
theorem inverse_isTriangulated :
    letI := c.commShift
    letI := c.inverseCommShift
    c.equivalence.inverse.IsTriangulated := by
  let := c.commShift
  let := c.inverseCommShift
  let : c.equivalence.toAdjunction.CommShift ℤ :=
    c.equivalence.toAdjunction.commShift_of_leftAdjoint ℤ
  let : c.equivalence.functor.IsTriangulated := c.isTriangulated
  exact c.equivalence.toAdjunction.isTriangulated_rightAdjoint

end Comparison

#print axioms Beilinson.ConcentratedDGA.Comparison.inverse_isTriangulated
#print axioms Beilinson.ConcentratedDGA.comparison
#print axioms Beilinson.ConcentratedDGA.eq_degreeZero_self

end Beilinson.ConcentratedDGA

module

public import StacksAlgebraProbe
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorAlgebra

/-! The compactness model and the geometric matrix model are the same subalgebra:
one is presented by algebra generation, the other by integer-indexed homogeneous entries. -/

set_option autoImplicit false

@[expose] public noncomputable section

open StacksDraft.Perfect Stacks.AlgebraicGeometry.ProjectiveGenerator

namespace Beilinson.MatrixAlgebraComparison

universe u
variable (k : Type u) [Field k] (n : ℕ)

/-- The generating set in the compactness model already is the geometric matrix subalgebra. -/
theorem algebra_eq : beilinsonAlgebra k n = endomorphismMatrices k n := by
  have hset : {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) k) |
      ∀ i j, (i ≤ j → (M i j).IsHomogeneous (j - i)) ∧ (j < i → M i j = 0)} =
      (endomorphismMatrices k n : Set _) := by
    ext M
    constructor
    · intro h
      change ∀ i j : Fin (n + 1), M i j ∈ homogeneousPiece k n ((j : ℤ) - (i : ℤ))
      intro i j
      by_cases hij : i ≤ j
      · rw [homogeneousPiece_of_nonneg k n (by have := Fin.le_def.1 hij; omega)]
        change (M i j).IsHomogeneous _
        convert (h i j).1 hij using 1
        omega
      · rw [(h i j).2 (lt_of_not_ge hij)]
        exact Submodule.zero_mem _
    · intro h i j
      exact ⟨fun hij => isHomogeneous_apply k n h hij,
        fun hji => apply_eq_zero_of_lt k n h hji⟩
  rw [beilinsonAlgebra, hset, Algebra.adjoin_eq]

/-- No change of coordinates or bases is needed to compare the two matrix models. -/
def algebraEquiv : beilinsonAlgebra k n ≃ₐ[k] endomorphismMatrices k n :=
  Subalgebra.equivOfEq _ _ (algebra_eq k n)

/-- The geometric matrix algebra is finite-dimensional, without choosing monomial bases. -/
theorem finite_matrix : Module.Finite k (endomorphismMatrices k n) := by
  let E (i j : Fin (n + 1)) :=
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k (j - i)
  have (i j : Fin (n + 1)) : Module.Finite k (E i j) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg _ k (j - i))
  let f : endomorphismMatrices k n →ₗ[k] (∀ i j : Fin (n + 1), E i j) :=
    { toFun M i j := ⟨M.val i j, by
        by_cases hij : i ≤ j
        · exact isHomogeneous_apply k n M.property hij
        · rw [apply_eq_zero_of_lt k n M.property (lt_of_not_ge hij)]
          exact Submodule.zero_mem _⟩
      map_add' _ _ := by ext i j; rfl
      map_smul' _ _ := by ext i j; rfl }
  apply Module.Finite.of_injective f
  intro M N h
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact congrArg Subtype.val (congrFun (congrFun h i) j)

/-- The finite-dimensionality fact is available for the compactness presentation as well. -/
theorem finite_algebra : Module.Finite k (beilinsonAlgebra k n) := by
  let := finite_matrix k n
  exact Module.Finite.equiv (algebraEquiv k n).symm.toLinearEquiv

#print axioms finite_matrix
#print axioms finite_algebra
#print axioms algebra_eq
#print axioms algebraEquiv

end Beilinson.MatrixAlgebraComparison

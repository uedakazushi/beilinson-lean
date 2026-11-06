module

public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dimension.Constructions


/-!
# A concrete Kronecker algebra

The four-dimensional algebra with vertices `0`, `1` and two arrows `0 ⟶ 1`.
We realize it faithfully as matrices `[[a,0,0],[x,b,0],[y,0,b]]`.
Multiplication is composition: the later map is on the left, as in the book.
This constructs the algebraic model; identifying it with the geometric
endomorphism algebra or with a general path-algebra construction is separate.
-/

public section

open Module

namespace Beilinson.Kronecker

variable (k : Type*) [Field k]

/-- Coordinates are the two vertex coefficients followed by the two arrows. -/
def toMatrix (c : Fin 4 → k) : Matrix (Fin 3) (Fin 3) k :=
  ![![c 0, 0, 0], ![c 2, c 1, 0], ![c 3, 0, c 1]]

/-- The concrete Kronecker subalgebra of `3 × 3` matrices. -/
def subalgebra : Subalgebra k (Matrix (Fin 3) (Fin 3) k) where
  carrier := Set.range (toMatrix k)
  algebraMap_mem' r := by
    refine ⟨![r, r, 0, 0], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatrix, Matrix.algebraMap_eq_diagonal]
  add_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨c + d, ?_⟩
    ext i j
    simp only [Matrix.add_apply]
    fin_cases i <;> fin_cases j <;> simp [toMatrix]
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨![c 0 * d 0, c 1 * d 1,
      c 2 * d 0 + c 1 * d 2, c 3 * d 0 + c 1 * d 3], ?_⟩
    ext i j
    simp only [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [toMatrix, Fin.sum_univ_succ]

/-- The algebraic model of the `n = 1` Beilinson algebra. -/
abbrev Algebra := subalgebra k

/-- A linear coordinate system, including an explicit inverse. -/
def coordinates : (Fin 4 → k) ≃ₗ[k] Algebra k where
  toFun c := ⟨toMatrix k c, ⟨c, rfl⟩⟩
  invFun m := ![m.val 0 0, m.val 1 1, m.val 1 0, m.val 2 0]
  left_inv c := by
    ext i
    fin_cases i <;> simp [toMatrix]
  right_inv m := by
    apply Subtype.ext
    obtain ⟨c, hc⟩ := m.property
    simp only [← hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatrix]
  map_add' c d := by
    apply Subtype.ext
    change toMatrix k (c + d) = toMatrix k c + toMatrix k d
    ext i j
    simp only [Matrix.add_apply]
    fin_cases i <;> fin_cases j <;> simp [toMatrix]
  map_smul' r c := by
    apply Subtype.ext
    change toMatrix k (r • c) = r • toMatrix k c
    ext i j
    simp only [Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;> simp [toMatrix]

@[simp] theorem coordinates_symm_one :
    (coordinates k).symm 1 = ![1, 1, 0, 0] := by
  ext i
  fin_cases i <;> simp [coordinates]

@[simp] theorem coordinates_symm_algebraMap (r : k) :
    (coordinates k).symm (algebraMap k (Algebra k) r) = ![r, r, 0, 0] := by
  ext i
  fin_cases i <;> simp [coordinates, Matrix.algebraMap_eq_diagonal]

/-- In particular, the model is finite dimensional. -/
instance : FiniteDimensional k (Algebra k) :=
  (coordinates k).finiteDimensional

/-- Two stationary paths and two arrows give dimension four. -/
theorem finrank : Module.finrank k (Algebra k) = 4 := by
  rw [← (coordinates k).finrank_eq]
  simp

/-- Coordinate multiplication makes the convention on path composition explicit. -/
theorem coordinates_mul (c d : Fin 4 → k) :
    coordinates k c * coordinates k d =
      coordinates k ![c 0 * d 0, c 1 * d 1,
        c 2 * d 0 + c 1 * d 2, c 3 * d 0 + c 1 * d 3] := by
  apply Subtype.ext
  ext i j
  change (toMatrix k c * toMatrix k d) i j = _
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [coordinates, toMatrix, Fin.sum_univ_succ]

/-- The stationary path at the source vertex. -/
def e₀ : Algebra k := coordinates k ![1, 0, 0, 0]

/-- The stationary path at the target vertex. -/
def e₁ : Algebra k := coordinates k ![0, 1, 0, 0]

/-- One of the two arrows, parametrized by `Fin 2`. -/
def arrow (i : Fin 2) : Algebra k :=
  coordinates k ![0, 0, if i = 0 then 1 else 0, if i = 1 then 1 else 0]

@[simp] theorem coordinates_symm_e₀ :
    (coordinates k).symm (e₀ k) = ![1, 0, 0, 0] := by simp [e₀]

@[simp] theorem coordinates_symm_e₁ :
    (coordinates k).symm (e₁ k) = ![0, 1, 0, 0] := by simp [e₁]

@[simp] theorem coordinates_symm_arrow (i : Fin 2) :
    (coordinates k).symm (arrow k i) =
      ![0, 0, if i = 0 then 1 else 0, if i = 1 then 1 else 0] := by simp [arrow]

@[simp] theorem e₀_mul_e₀ : e₀ k * e₀ k = e₀ k := by
  simp [e₀, coordinates_mul]

@[simp] theorem e₁_mul_e₁ : e₁ k * e₁ k = e₁ k := by
  simp [e₁, coordinates_mul]

@[simp] theorem e₀_mul_e₁ : e₀ k * e₁ k = 0 := by
  simp [e₀, e₁, coordinates_mul]

@[simp] theorem e₁_mul_e₀ : e₁ k * e₀ k = 0 := by
  simp [e₀, e₁, coordinates_mul]

@[simp] theorem e₀_add_e₁ : e₀ k + e₁ k = 1 := by
  apply Subtype.ext
  ext i j
  change (toMatrix k ![1, 0, 0, 0] + toMatrix k ![0, 1, 0, 0]) i j = _
  simp only [Matrix.add_apply]
  fin_cases i <;> fin_cases j <;> simp [toMatrix]

@[simp] theorem e₁_mul_arrow (i : Fin 2) : e₁ k * arrow k i = arrow k i := by
  simp [e₁, arrow, coordinates_mul]

@[simp] theorem arrow_mul_e₀ (i : Fin 2) : arrow k i * e₀ k = arrow k i := by
  simp [e₀, arrow, coordinates_mul]

@[simp] theorem e₀_mul_arrow (i : Fin 2) : e₀ k * arrow k i = 0 := by
  simp [e₀, arrow, coordinates_mul]

@[simp] theorem arrow_mul_e₁ (i : Fin 2) : arrow k i * e₁ k = 0 := by
  simp [e₁, arrow, coordinates_mul]

/-- No two arrows are composable. -/
@[simp] theorem arrow_mul_arrow (i j : Fin 2) : arrow k i * arrow k j = 0 := by
  simp [arrow, coordinates_mul]

/-- The stationary paths and arrows form a basis, with no additional relations. -/
noncomputable def basis : Basis (Fin 4) k (Algebra k) :=
  (Pi.basisFun k (Fin 4)).map (coordinates k)

@[simp] theorem basis_zero : basis k 0 = e₀ k := by
  apply congrArg (coordinates k)
  change Pi.basisFun k (Fin 4) 0 = _
  ext i
  fin_cases i <;> simp

@[simp] theorem basis_one : basis k 1 = e₁ k := by
  apply congrArg (coordinates k)
  change Pi.basisFun k (Fin 4) 1 = _
  ext i
  fin_cases i <;> simp

@[simp] theorem basis_two : basis k 2 = arrow k 0 := by
  apply congrArg (coordinates k)
  change Pi.basisFun k (Fin 4) 2 = _
  ext i
  fin_cases i <;> simp

@[simp] theorem basis_three : basis k 3 = arrow k 1 := by
  apply congrArg (coordinates k)
  change Pi.basisFun k (Fin 4) 3 = _
  ext i
  fin_cases i <;> simp

/-- Expansion in the two stationary paths and the two arrows. -/
theorem coordinates_eq (c : Fin 4 → k) :
    coordinates k c = c 0 • e₀ k + c 1 • e₁ k +
      c 2 • arrow k 0 + c 3 • arrow k 1 := by
  apply (coordinates k).symm.injective
  simp only [map_add, map_smul, LinearEquiv.symm_apply_apply,
    coordinates_symm_e₀, coordinates_symm_e₁, coordinates_symm_arrow]
  ext i
  fin_cases i <;> simp

end Beilinson.Kronecker

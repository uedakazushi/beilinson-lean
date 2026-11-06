module

public import Beilinson.Kronecker
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Right Kronecker modules and reverse arrows

Right actions are algebra maps from the opposite algebra to linear endomorphisms.
For the book's multiplication convention an arrow `0 ⟶ 1` acts from the vertex-1
space to the vertex-0 space. This file constructs such actions from two linear
maps and decomposes every right action into its vertex spaces.
-/

@[expose] public section

open Module MulOpposite

namespace Beilinson.Kronecker

variable {k : Type*} [Field k]

section FromArrows

variable {V₀ V₁ : Type*} [AddCommGroup V₀] [Module k V₀]
  [AddCommGroup V₁] [Module k V₁]

/-- Right multiplication in coordinates on a pair of vertex spaces. -/
def actionOfArrows (f : Fin 2 → V₁ →ₗ[k] V₀) (a : Algebra k) :
    Module.End k (V₀ × V₁) where
  toFun m :=
    let c := (coordinates k).symm a
    (c 0 • m.1 + c 2 • f 0 m.2 + c 3 • f 1 m.2, c 1 • m.2)
  map_add' m n := by
    dsimp
    simp only [map_add, smul_add]
    (ext <;> dsimp)
    abel
  map_smul' r m := by
    dsimp
    simp only [map_smul, smul_smul]
    ext <;> dsimp
    · module
    · rw [mul_comm]

@[simp] theorem actionOfArrows_coordinates (f : Fin 2 → V₁ →ₗ[k] V₀)
    (c : Fin 4 → k) (m : V₀ × V₁) :
    actionOfArrows f (coordinates k c) m =
      (c 0 • m.1 + c 2 • f 0 m.2 + c 3 • f 1 m.2, c 1 • m.2) := by
  simp [actionOfArrows]

/-- Two maps `V₁ ⟶ V₀` define a right Kronecker action. -/
def ofArrows (f : Fin 2 → V₁ →ₗ[k] V₀) :
    (Algebra k)ᵐᵒᵖ →ₐ[k] Module.End k (V₀ × V₁) where
  toFun a := actionOfArrows f a.unop
  map_zero' := by
    apply LinearMap.ext
    intro m
    apply Prod.ext <;> simp [actionOfArrows]
  map_one' := by
    apply LinearMap.ext
    intro m
    apply Prod.ext <;> simp [actionOfArrows]
  map_add' a b := by
    apply LinearMap.ext
    intro m
    (apply Prod.ext <;> simp [actionOfArrows, add_smul])
    module
  map_mul' a b := by
    obtain ⟨c, hc⟩ := (coordinates k).surjective a.unop
    obtain ⟨d, hd⟩ := (coordinates k).surjective b.unop
    apply LinearMap.ext
    intro m
    change actionOfArrows f (b.unop * a.unop) m =
      actionOfArrows f a.unop (actionOfArrows f b.unop m)
    simp only [← hc, ← hd, coordinates_mul, actionOfArrows_coordinates]
    simp only [map_smul]
    apply Prod.ext <;> dsimp <;> module
  commutes' r := by
    apply LinearMap.ext
    intro m
    apply Prod.ext <;> simp [actionOfArrows]

/-- The actual module structure associated to the constructed right action.
This is a definition rather than a global instance, since the action depends on `f`. -/
@[instance_reducible] def moduleOfArrows (f : Fin 2 → V₁ →ₗ[k] V₀) : Module (Algebra k)ᵐᵒᵖ (V₀ × V₁) :=
  Module.compHom (V₀ × V₁) (ofArrows f).toRingHom

/-- The constructed module has the given scalar action of the ground field. -/
theorem moduleOfArrows_isScalarTower (f : Fin 2 → V₁ →ₗ[k] V₀) :
    letI := moduleOfArrows f
    IsScalarTower k (Algebra k)ᵐᵒᵖ (V₀ × V₁) := by
  let := moduleOfArrows f
  constructor
  intro r a m
  change ofArrows f (r • a) m = r • ofArrows f a m
  rw [map_smul]
  rfl

/-- The right action commutes with the ground-field action. -/
theorem moduleOfArrows_smulCommClass (f : Fin 2 → V₁ →ₗ[k] V₀) :
    letI := moduleOfArrows f
    SMulCommClass (Algebra k)ᵐᵒᵖ k (V₀ × V₁) := by
  let := moduleOfArrows f
  constructor
  intro a r m
  exact map_smul (ofArrows f a) r m

@[simp] theorem ofArrows_e₀ (f : Fin 2 → V₁ →ₗ[k] V₀) (m : V₀ × V₁) :
    ofArrows f (op (e₀ k)) m = (m.1, 0) := by
  simp [ofArrows, actionOfArrows]

@[simp] theorem ofArrows_e₁ (f : Fin 2 → V₁ →ₗ[k] V₀) (m : V₀ × V₁) :
    ofArrows f (op (e₁ k)) m = (0, m.2) := by
  simp [ofArrows, actionOfArrows]

@[simp] theorem ofArrows_arrow (f : Fin 2 → V₁ →ₗ[k] V₀)
    (i : Fin 2) (m : V₀ × V₁) :
    ofArrows f (op (arrow k i)) m = (f i m.2, 0) := by
  fin_cases i <;> simp [ofArrows, actionOfArrows]

section Morphisms

variable {W₀ W₁ : Type*} [AddCommGroup W₀] [Module k W₀]
  [AddCommGroup W₁] [Module k W₁]

/-- A pair of vertex maps is a right-module intertwiner exactly when the two
reverse-arrow squares commute. -/
theorem prodMap_intertwines_iff (f : Fin 2 → V₁ →ₗ[k] V₀)
    (g : Fin 2 → W₁ →ₗ[k] W₀) (u₀ : V₀ →ₗ[k] W₀) (u₁ : V₁ →ₗ[k] W₁) :
    (∀ (a : (Algebra k)ᵐᵒᵖ) (m : V₀ × V₁),
      (u₀.prodMap u₁) (ofArrows f a m) = ofArrows g a ((u₀.prodMap u₁) m)) ↔
      ∀ i, u₀.comp (f i) = (g i).comp u₁ := by
  constructor
  · intro h i
    apply LinearMap.ext
    intro v
    have hv := congrArg Prod.fst (h (op (arrow k i)) (0, v))
    simpa using hv
  · intro h a m
    change (u₀.prodMap u₁) (actionOfArrows f a.unop m) =
      actionOfArrows g a.unop ((u₀.prodMap u₁) m)
    have h₀ := LinearMap.congr_fun (h 0) m.2
    have h₁ := LinearMap.congr_fun (h 1) m.2
    simp only [LinearMap.comp_apply] at h₀ h₁
    apply Prod.ext
    · simp [actionOfArrows, h₀, h₁]
    · simp [actionOfArrows]

end Morphisms

end FromArrows

section ToArrows

variable {M : Type*} [AddCommGroup M] [Module k M]
  (ρ : (Algebra k)ᵐᵒᵖ →ₐ[k] Module.End k M)

/-- The subspace fixed by the action of a vertex idempotent. -/
def vertex (e : Algebra k) : Submodule k M where
  carrier := {m | ρ (op e) m = m}
  zero_mem' := map_zero _
  add_mem' {x y} hx hy := by
    change ρ (op e) x = x at hx
    change ρ (op e) y = y at hy
    change ρ (op e) (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' r m hm := by
    change ρ (op e) m = m at hm
    change ρ (op e) (r • m) = r • m
    rw [map_smul, hm]

/-- Composition of right multiplications reverses the order in the algebra. -/
theorem act_act (a b : Algebra k) (m : M) :
    ρ (op a) (ρ (op b) m) = ρ (op (b * a)) m := by
  rw [← Module.End.mul_apply, ← map_mul]
  rfl

/-- The sum of the two vertex projections is the identity. -/
theorem vertex_sum (m : M) : ρ (op (e₀ k)) m + ρ (op (e₁ k)) m = m := by
  rw [← LinearMap.add_apply, ← map_add, ← op_add, e₀_add_e₁, op_one, map_one]
  rfl

/-- Projection to vertex 0. -/
def project₀ : M →ₗ[k] vertex ρ (e₀ k) where
  toFun m := ⟨ρ (op (e₀ k)) m, by
    change ρ (op (e₀ k)) (ρ (op (e₀ k)) m) = _
    rw [act_act, e₀_mul_e₀]⟩
  map_add' m n := Subtype.ext (map_add _ m n)
  map_smul' r m := Subtype.ext (map_smul _ r m)

/-- Projection to vertex 1. -/
def project₁ : M →ₗ[k] vertex ρ (e₁ k) where
  toFun m := ⟨ρ (op (e₁ k)) m, by
    change ρ (op (e₁ k)) (ρ (op (e₁ k)) m) = _
    rw [act_act, e₁_mul_e₁]⟩
  map_add' m n := Subtype.ext (map_add _ m n)
  map_smul' r m := Subtype.ext (map_smul _ r m)

@[simp] theorem act_e₀_vertex₁ (m : vertex ρ (e₁ k)) : ρ (op (e₀ k)) m = 0 := by
  rw [← m.property, act_act, e₁_mul_e₀, op_zero, map_zero]
  rfl

@[simp] theorem act_e₁_vertex₀ (m : vertex ρ (e₀ k)) : ρ (op (e₁ k)) m = 0 := by
  rw [← m.property, act_act, e₀_mul_e₁, op_zero, map_zero]
  rfl

/-- Each original arrow acts in the reverse direction on right modules. -/
def arrowMap (i : Fin 2) : vertex ρ (e₁ k) →ₗ[k] vertex ρ (e₀ k) where
  toFun m := ⟨ρ (op (arrow k i)) m, by
    change ρ (op (e₀ k)) (ρ (op (arrow k i)) m) = _
    rw [act_act, arrow_mul_e₀]⟩
  map_add' m n := by
    apply Subtype.ext
    exact map_add (ρ (op (arrow k i))) m.val n.val
  map_smul' r m := by
    apply Subtype.ext
    exact map_smul (ρ (op (arrow k i))) r m.val

/-- Every right action splits canonically into its two vertex spaces. -/
def decompose : M ≃ₗ[k] (vertex ρ (e₀ k) × vertex ρ (e₁ k)) where
  toFun m := (project₀ ρ m, project₁ ρ m)
  invFun m := m.1.val + m.2.val
  left_inv := vertex_sum ρ
  right_inv m := by
    apply Prod.ext <;> apply Subtype.ext
    · change ρ (op (e₀ k)) (m.1.val + m.2.val) = m.1.val
      rw [map_add, m.1.property, act_e₀_vertex₁, add_zero]
    · change ρ (op (e₁ k)) (m.1.val + m.2.val) = m.2.val
      rw [map_add, act_e₁_vertex₀, m.2.property, zero_add]
  map_add' m n := by simp only [map_add, Prod.mk_add_mk]
  map_smul' r m := by simp only [map_smul, Prod.smul_mk, RingHom.id_apply]

/-- Finite-dimensional modules split with additive vertex dimensions. -/
theorem finrank_vertices [FiniteDimensional k M] :
    Module.finrank k M = Module.finrank k (vertex ρ (e₀ k)) +
      Module.finrank k (vertex ρ (e₁ k)) := by
  rw [(decompose ρ).finrank_eq, Module.finrank_prod]

/-- A general right action is the action of its four path coefficients. -/
theorem act_coordinates (c : Fin 4 → k) (m : M) :
    ρ (op (coordinates k c)) m =
      c 0 • ρ (op (e₀ k)) m + c 1 • ρ (op (e₁ k)) m +
        c 2 • ρ (op (arrow k 0)) m + c 3 • ρ (op (arrow k 1)) m := by
  rw [coordinates_eq]
  simp only [op_add, op_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]

/-- Under the vertex decomposition, the original action is exactly the one
reconstructed from its two reverse arrows. -/
theorem decompose_action (a : Algebra k) (m : M) :
    decompose ρ (ρ (op a) m) = ofArrows (arrowMap ρ) (op a) (decompose ρ m) := by
  obtain ⟨c, rfl⟩ := (coordinates k).surjective a
  apply (decompose ρ).symm.injective
  simp only [LinearEquiv.symm_apply_apply]
  change ρ (op (coordinates k c)) m =
    (actionOfArrows (arrowMap ρ) (coordinates k c)
      (project₀ ρ m, project₁ ρ m)).1.val +
    (actionOfArrows (arrowMap ρ) (coordinates k c)
      (project₀ ρ m, project₁ ρ m)).2.val
  rw [act_coordinates, actionOfArrows_coordinates]
  change _ = (c 0 • ρ (op (e₀ k)) m +
    c 2 • ρ (op (arrow k 0)) (ρ (op (e₁ k)) m) +
    c 3 • ρ (op (arrow k 1)) (ρ (op (e₁ k)) m)) + c 1 • ρ (op (e₁ k)) m
  rw [act_act, act_act, e₁_mul_arrow, e₁_mul_arrow]
  abel

/-- Standard mathlib modules over the opposite algebra supply the right actions used above. -/
def actionOfModule [Module (Algebra k)ᵐᵒᵖ M] [IsScalarTower k (Algebra k)ᵐᵒᵖ M]
    [SMulCommClass (Algebra k)ᵐᵒᵖ k M] :
    (Algebra k)ᵐᵒᵖ →ₐ[k] Module.End k M :=
  _root_.Algebra.lsmul k k M

section Intertwiners

variable {N : Type*} [AddCommGroup N] [Module k N]
  (σ : (Algebra k)ᵐᵒᵖ →ₐ[k] Module.End k N)
  (φ : M →ₗ[k] N) (hφ : ∀ a m, φ (ρ a m) = σ a (φ m))

/-- Every module intertwiner restricts to a map of each vertex space. -/
def vertexMap (e : Algebra k) : vertex ρ e →ₗ[k] vertex σ e where
  toFun m := ⟨φ m, by
    change σ (op e) (φ m.val) = φ m.val
    rw [← hφ, m.property]⟩
  map_add' m n := by
    apply Subtype.ext
    exact map_add φ m.val n.val
  map_smul' r m := by
    apply Subtype.ext
    exact map_smul φ r m.val

/-- Restricted vertex maps commute with the reverse arrows. -/
theorem vertexMap_arrow (i : Fin 2) :
    (vertexMap ρ σ φ hφ (e₀ k)).comp (arrowMap ρ i) =
      (arrowMap σ i).comp (vertexMap ρ σ φ hφ (e₁ k)) := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  exact hφ (op (arrow k i)) m.val

/-- In vertex coordinates every module intertwiner is the product of its restrictions. -/
theorem decompose_intertwiner (m : M) :
    decompose σ (φ m) =
      ((vertexMap ρ σ φ hφ (e₀ k)).prodMap
        (vertexMap ρ σ φ hφ (e₁ k))) (decompose ρ m) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact (hφ (op (e₀ k)) m).symm
  · exact (hφ (op (e₁ k)) m).symm

end Intertwiners

end ToArrows

/-- Converting the constructed module back to an algebra action recovers `ofArrows`. -/
theorem actionOfModule_ofArrows {V₀ V₁ : Type*} [AddCommGroup V₀] [Module k V₀]
    [AddCommGroup V₁] [Module k V₁] (f : Fin 2 → V₁ →ₗ[k] V₀) :
    letI := moduleOfArrows f
    letI := moduleOfArrows_isScalarTower f
    letI := moduleOfArrows_smulCommClass f
    actionOfModule (M := V₀ × V₁) = ofArrows f := by
  rfl

end Beilinson.Kronecker

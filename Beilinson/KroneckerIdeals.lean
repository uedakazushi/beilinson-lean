module

public import Beilinson.KroneckerDimension

/-!
# Vertex right ideals

The fixed submodule for left multiplication by an idempotent is its principal
right ideal. The two vertex right ideals give the usual sink and source
projective representations of the reverse Kronecker quiver.
-/

@[expose] public section

open CategoryTheory Module MulOpposite

universe u

namespace Beilinson.Kronecker

variable (k : Type u) [Field k]

/-- The fixed submodule of left multiplication, with the regular right action. -/
def fixedLeft (e : Algebra k) : Submodule (Algebra k)ᵐᵒᵖ (Algebra k) where
  carrier := {a | e * a = a}
  zero_mem' := mul_zero _
  add_mem' {a b} ha hb := by
    change e * a = a at ha
    change e * b = b at hb
    change e * (a + b) = a + b
    rw [mul_add, ha, hb]
  smul_mem' r a ha := by
    change e * a = a at ha
    change e * (a * r.unop) = a * r.unop
    rw [← mul_assoc, ha]

/-- For an idempotent e, the fixed submodule is exactly the right ideal eA. -/
theorem mem_fixedLeft_iff (e : Algebra k) (he : e * e = e) (a : Algebra k) :
    a ∈ fixedLeft k e ↔ ∃ b : Algebra k, e * b = a := by
  constructor
  · intro h
    exact ⟨a, h⟩
  · rintro ⟨b, rfl⟩
    change e * (e * b) = e * b
    rw [← mul_assoc, he]

@[simp] theorem e₀_mul_coordinates (c : Fin 4 → k) :
    e₀ k * coordinates k c = coordinates k ![c 0, 0, 0, 0] := by
  rw [← (coordinates k).apply_symm_apply (e₀ k), coordinates_symm_e₀, coordinates_mul]
  simp

@[simp] theorem e₁_mul_coordinates (c : Fin 4 → k) :
    e₁ k * coordinates k c = coordinates k ![0, c 1, c 2, c 3] := by
  rw [← (coordinates k).apply_symm_apply (e₁ k), coordinates_symm_e₁, coordinates_mul]
  simp

/-- The principal right ideal at vertex 0. -/
abbrev vertexIdeal₀ := fixedLeft k (e₀ k)

/-- The principal right ideal at vertex 1. -/
abbrev vertexIdeal₁ := fixedLeft k (e₁ k)

/-- The representation of the source projective, with its two inclusion arrows. -/
def sourceProjective : ReverseRep.{u,u} k where
  V₀ := ModuleCat.of k (k × k)
  V₁ := ModuleCat.of k k
  arrow i := if i = 0 then LinearMap.inl k k k else LinearMap.inr k k k

/-- Extract the scalar from the sink module, with its ground-field type explicit. -/
def sinkScalar (m : fromReverseRep.obj (ReverseRep.sink (ModuleCat.of k k))) : k := m.1

/-- The scalar coordinate of the sink's right action. -/
theorem sink_action (r : (Algebra k)ᵐᵒᵖ)
    (m : fromReverseRep.obj (ReverseRep.sink (ModuleCat.of k k))) :
    sinkScalar k (r • m) = (coordinates k).symm r.unop 0 * sinkScalar k m := by
  change ((coordinates k).symm r.unop 0 * sinkScalar k m +
    (coordinates k).symm r.unop 2 * 0 + (coordinates k).symm r.unop 3 * 0) = _
  simp

/-- The sink projective is precisely the principal right ideal e₀A. -/
def sinkIdealEquiv :
    fromReverseRep.obj (ReverseRep.sink (ModuleCat.of k k)) ≃ₗ[(Algebra k)ᵐᵒᵖ]
      vertexIdeal₀ k where
  toFun m := ⟨coordinates k ![m.1, 0, 0, 0], by
    change e₀ k * coordinates k ![m.1, 0, 0, 0] = _
    exact e₀_mul_coordinates k _⟩
  invFun a := ((coordinates k).symm a.val 0, PUnit.unit)
  left_inv m := by
    apply Prod.ext
    · exact congrFun ((coordinates k).symm_apply_apply ![m.1, 0, 0, 0]) 0
    · exact Subsingleton.elim (α := PUnit.{u+1}) _ _
  right_inv a := by
    apply Subtype.ext
    calc
      coordinates k ![(coordinates k).symm a.val 0, 0, 0, 0] =
          e₀ k * coordinates k ((coordinates k).symm a.val) :=
        (e₀_mul_coordinates k _).symm
      _ = e₀ k * a.val := congrArg (fun b => e₀ k * b) ((coordinates k).apply_symm_apply a.val)
      _ = a.val := a.property
  map_add' m n := by
    apply Subtype.ext
    change coordinates k ![sinkScalar k m + sinkScalar k n, 0, 0, 0] =
      coordinates k ![m.1, 0, 0, 0] + coordinates k ![n.1, 0, 0, 0]
    apply (coordinates k).symm.injective
    simp only [map_add, LinearEquiv.symm_apply_apply]
    ext i
    (fin_cases i <;> simp)
    rfl
  map_smul' r m := by
    apply Subtype.ext
    change coordinates k ![sinkScalar k (r • m), 0, 0, 0] =
      coordinates k ![m.1, 0, 0, 0] * r.unop
    rw [sink_action]
    calc
      coordinates k ![(coordinates k).symm r.unop 0 * sinkScalar k m, 0, 0, 0] =
          coordinates k ![m.1, 0, 0, 0] * coordinates k ((coordinates k).symm r.unop) := by
        rw [coordinates_mul]
        apply congrArg (coordinates k)
        ext i
        fin_cases i
        · exact mul_comm ((coordinates k).symm r.unop 0) (sinkScalar k m)
        · simp
        · simp
        · simp
      _ = _ := congrArg (fun b => coordinates k ![m.1, 0, 0, 0] * b)
        ((coordinates k).apply_symm_apply r.unop)

/-- Coordinates of the source projective in the order (0,b,x,y). -/
def sourceCoords (m : fromReverseRep.obj (sourceProjective k)) : Fin 4 → k :=
  ![0, m.2, m.1.1, m.1.2]

/-- The source projective's right action, expressed in algebra coordinates. -/
theorem sourceCoords_action (r : (Algebra k)ᵐᵒᵖ)
    (m : fromReverseRep.obj (sourceProjective k)) :
    sourceCoords k (r • m) =
      ![0, (coordinates k).symm r.unop 1 * sourceCoords k m 1,
        (coordinates k).symm r.unop 0 * sourceCoords k m 2 +
          (coordinates k).symm r.unop 2 * sourceCoords k m 1,
        (coordinates k).symm r.unop 0 * sourceCoords k m 3 +
          (coordinates k).symm r.unop 3 * sourceCoords k m 1] := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · change ((coordinates k).symm r.unop 0 * sourceCoords k m 2 +
      (coordinates k).symm r.unop 2 * sourceCoords k m 1) +
      (coordinates k).symm r.unop 3 * 0 = _
    simp
  · change ((coordinates k).symm r.unop 0 * sourceCoords k m 3 +
      (coordinates k).symm r.unop 2 * 0) +
      (coordinates k).symm r.unop 3 * sourceCoords k m 1 = _
    simp

/-- The source projective is precisely the principal right ideal e₁A. -/
def sourceIdealEquiv :
    fromReverseRep.obj (sourceProjective k) ≃ₗ[(Algebra k)ᵐᵒᵖ] vertexIdeal₁ k where
  toFun m := ⟨coordinates k (sourceCoords k m), by
    change e₁ k * coordinates k ![0, m.2, m.1.1, m.1.2] = _
    exact e₁_mul_coordinates k _⟩
  invFun a := (((coordinates k).symm a.val 2, (coordinates k).symm a.val 3),
    (coordinates k).symm a.val 1)
  left_inv m := by
    have h := (coordinates k).symm_apply_apply (sourceCoords k m)
    apply Prod.ext
    · apply Prod.ext
      · exact congrFun h 2
      · exact congrFun h 3
    · exact congrFun h 1
  right_inv a := by
    apply Subtype.ext
    calc
      coordinates k ![0, (coordinates k).symm a.val 1, (coordinates k).symm a.val 2,
          (coordinates k).symm a.val 3] =
          e₁ k * coordinates k ((coordinates k).symm a.val) :=
        (e₁_mul_coordinates k _).symm
      _ = e₁ k * a.val := congrArg (fun b => e₁ k * b) ((coordinates k).apply_symm_apply a.val)
      _ = a.val := a.property
  map_add' m n := by
    apply Subtype.ext
    apply (coordinates k).symm.injective
    simp only [LinearEquiv.symm_apply_apply]
    ext i
    fin_cases i <;> simp [sourceCoords] <;> rfl
  map_smul' r m := by
    apply Subtype.ext
    change coordinates k (sourceCoords k (r • m)) =
      coordinates k (sourceCoords k m) * r.unop
    rw [sourceCoords_action]
    calc
      coordinates k ![0, (coordinates k).symm r.unop 1 * sourceCoords k m 1,
          (coordinates k).symm r.unop 0 * sourceCoords k m 2 +
            (coordinates k).symm r.unop 2 * sourceCoords k m 1,
          (coordinates k).symm r.unop 0 * sourceCoords k m 3 +
            (coordinates k).symm r.unop 3 * sourceCoords k m 1] =
          coordinates k (sourceCoords k m) * coordinates k ((coordinates k).symm r.unop) := by
        rw [coordinates_mul]
        apply congrArg (coordinates k)
        ext i
        fin_cases i
        · simp [sourceCoords]
        · exact mul_comm ((coordinates k).symm r.unop 1) (sourceCoords k m 1)
        · exact congrArg₂ (fun a b : k => a + b)
            (mul_comm ((coordinates k).symm r.unop 0) (sourceCoords k m 2))
            (mul_comm ((coordinates k).symm r.unop 2) (sourceCoords k m 1))
        · exact congrArg₂ (fun a b : k => a + b)
            (mul_comm ((coordinates k).symm r.unop 0) (sourceCoords k m 3))
            (mul_comm ((coordinates k).symm r.unop 3) (sourceCoords k m 1))
      _ = _ := congrArg (fun b => coordinates k (sourceCoords k m) * b)
        ((coordinates k).apply_symm_apply r.unop)

/-- Removing the zero summand identifies the cover of the source simple with the source projective. -/
def sourceProjectiveIso : ReverseRep.cover (sourceSimple k) ≅ sourceProjective k where
  hom :=
    { zero := LinearMap.snd k PUnit.{u+1} (k × k)
      one := LinearMap.id
      comm i := by fin_cases i <;> rfl }
  inv :=
    { zero := LinearMap.inr k PUnit.{u+1} (k × k)
      one := LinearMap.id
      comm i := by fin_cases i <;> rfl }
  hom_inv_id := by
    apply ReverseRep.hom_ext
    · ext m
      apply Prod.ext
      · exact Subsingleton.elim (α := PUnit.{u+1}) _ _
      · rfl
    · rfl
  inv_hom_id := by apply ReverseRep.hom_ext <;> rfl

instance sourceProjective_projective : Projective (sourceProjective k) :=
  Projective.of_iso (sourceProjectiveIso k) inferInstance

/-- The principal right ideal e₀A is a categorical projective right module. -/
instance vertexIdeal₀_projective : Projective (ModuleCat.of (Algebra k)ᵐᵒᵖ (vertexIdeal₀ k)) :=
  Projective.of_iso (sinkIdealEquiv k).toModuleIso
    ((moduleEquivalence.symm.map_projective_iff (ReverseRep.sink (ModuleCat.of k k))).mpr inferInstance)

/-- The principal right ideal e₁A is a categorical projective right module. -/
instance vertexIdeal₁_projective : Projective (ModuleCat.of (Algebra k)ᵐᵒᵖ (vertexIdeal₁ k)) :=
  Projective.of_iso (sourceIdealEquiv k).toModuleIso
    ((moduleEquivalence.symm.map_projective_iff (sourceProjective k)).mpr inferInstance)

/-- The categorical and algebraic projectivity notions agree for the first ideal. -/
theorem vertexIdeal₀_module_projective : Module.Projective (Algebra k)ᵐᵒᵖ (vertexIdeal₀ k) :=
  ModuleCat.projective_of_module_projective (ModuleCat.of (Algebra k)ᵐᵒᵖ (vertexIdeal₀ k))

/-- The categorical and algebraic projectivity notions agree for the second ideal. -/
theorem vertexIdeal₁_module_projective : Module.Projective (Algebra k)ᵐᵒᵖ (vertexIdeal₁ k) :=
  ModuleCat.projective_of_module_projective (ModuleCat.of (Algebra k)ᵐᵒᵖ (vertexIdeal₁ k))

/-- The regular right module splits as the two principal vertex right ideals. -/
def vertexIdealDecomposition :
    Algebra k ≃ₗ[(Algebra k)ᵐᵒᵖ] (vertexIdeal₀ k × vertexIdeal₁ k) where
  toFun a :=
    (⟨e₀ k * a, by change e₀ k * (e₀ k * a) = _; rw [← mul_assoc, e₀_mul_e₀]⟩,
     ⟨e₁ k * a, by change e₁ k * (e₁ k * a) = _; rw [← mul_assoc, e₁_mul_e₁]⟩)
  invFun m := m.1.val + m.2.val
  left_inv a := by
    change e₀ k * a + e₁ k * a = a
    rw [← add_mul, e₀_add_e₁, one_mul]
  right_inv m := by
    have h₀₁ : e₀ k * m.2.val = 0 := by
      calc
        e₀ k * m.2.val = e₀ k * (e₁ k * m.2.val) :=
          congrArg (fun a => e₀ k * a) m.2.property.symm
        _ = (e₀ k * e₁ k) * m.2.val := (mul_assoc _ _ _).symm
        _ = 0 := by rw [e₀_mul_e₁, zero_mul]
    have h₁₀ : e₁ k * m.1.val = 0 := by
      calc
        e₁ k * m.1.val = e₁ k * (e₀ k * m.1.val) :=
          congrArg (fun a => e₁ k * a) m.1.property.symm
        _ = (e₁ k * e₀ k) * m.1.val := (mul_assoc _ _ _).symm
        _ = 0 := by rw [e₁_mul_e₀, zero_mul]
    apply Prod.ext <;> apply Subtype.ext
    · change e₀ k * (m.1.val + m.2.val) = m.1.val
      rw [mul_add, m.1.property, h₀₁, add_zero]
    · change e₁ k * (m.1.val + m.2.val) = m.2.val
      rw [mul_add, h₁₀, m.2.property, zero_add]
  map_add' a b := by
    apply Prod.ext <;> apply Subtype.ext
    · exact mul_add _ _ _
    · exact mul_add _ _ _
  map_smul' r a := by
    apply Prod.ext <;> apply Subtype.ext
    · change e₀ k * (a * r.unop) = (e₀ k * a) * r.unop
      exact (mul_assoc _ _ _).symm
    · change e₁ k * (a * r.unop) = (e₁ k * a) * r.unop
      exact (mul_assoc _ _ _).symm

end Beilinson.Kronecker

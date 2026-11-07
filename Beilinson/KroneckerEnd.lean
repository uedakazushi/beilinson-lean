module

public import Beilinson.Kronecker
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Tactic.Abel

/-! The Kronecker algebra acts on a binary biproduct through two chosen morphisms.
With scalar diagonal endomorphisms, zero reverse Hom, and a basis of the forward
Hom, this will identify the complete endomorphism algebra of the biproduct. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Beilinson.KroneckerEnd

universe u v w

variable (k : Type u) [Field k] {C : Type w} [Category.{v} C]
  [Preadditive C] [Linear k C] [HasBinaryBiproducts C] {X Y : C}

/-- The two scalar diagonal blocks and the two chosen off-diagonal morphisms. -/
def fromCoordinates (f : Fin 2 → (X ⟶ Y)) : (Fin 4 → k) →ₗ[k] End (X ⊞ Y) where
  toFun c := .of (Biprod.ofComponents (c 0 • 𝟙 X) (c 2 • f 0 + c 3 • f 1) 0 (c 1 • 𝟙 Y))
  map_add' c d := by
    ext <;> simp [Biprod.ofComponents, add_smul, Linear.smul_comp, Linear.comp_smul]
    abel
  map_smul' r c := by
    ext <;> simp [Biprod.ofComponents, smul_add, smul_smul, smul_eq_mul,
      Linear.smul_comp, Linear.comp_smul]

/-- The later endomorphism is on the left in the product. -/
theorem fromCoordinates_mul (f : Fin 2 → (X ⟶ Y)) (c d : Fin 4 → k) :
    fromCoordinates k f ![c 0 * d 0, c 1 * d 1,
      c 2 * d 0 + c 1 * d 2, c 3 * d 0 + c 1 * d 3] =
      fromCoordinates k f c * fromCoordinates k f d := by
  apply End.ext
  change Biprod.ofComponents ((c 0 * d 0) • 𝟙 X)
      ((c 2 * d 0 + c 1 * d 2) • f 0 + (c 3 * d 0 + c 1 * d 3) • f 1)
      0 ((c 1 * d 1) • 𝟙 Y) =
    Biprod.ofComponents (d 0 • 𝟙 X) (d 2 • f 0 + d 3 • f 1) 0 (d 1 • 𝟙 Y) ≫
      Biprod.ofComponents (c 0 • 𝟙 X) (c 2 • f 0 + c 3 • f 1) 0 (c 1 • 𝟙 Y)
  rw [Biprod.ofComponents_comp]
  congr 1 <;> simp [Linear.smul_comp, Linear.comp_smul, smul_smul,
    add_smul, smul_add, mul_comm]
  abel

/-- The sum of the two scalar diagonal blocks is the identity. -/
theorem fromCoordinates_one (f : Fin 2 → (X ⟶ Y)) :
    fromCoordinates k f ![1, 1, 0, 0] = 1 := by
  ext <;> simp [fromCoordinates, Biprod.ofComponents]

/-- Two morphisms define a unital action of the concrete Kronecker algebra. -/
def ofArrows (f : Fin 2 → (X ⟶ Y)) : Kronecker.Algebra k →ₐ[k] End (X ⊞ Y) :=
  AlgHom.ofLinearMap
    ((fromCoordinates k f).comp (Kronecker.coordinates k).symm.toLinearMap)
    (by simpa using fromCoordinates_one k f)
    (by
      intro a b
      obtain ⟨c, rfl⟩ := (Kronecker.coordinates k).surjective a
      obtain ⟨d, rfl⟩ := (Kronecker.coordinates k).surjective b
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        Kronecker.coordinates_mul, LinearEquiv.symm_apply_apply] using
        fromCoordinates_mul k f c d)

@[simp] theorem ofArrows_coordinates (f : Fin 2 → (X ⟶ Y)) (c : Fin 4 → k) :
    ofArrows k f (Kronecker.coordinates k c) = fromCoordinates k f c := by
  change fromCoordinates k f ((Kronecker.coordinates k).symm (Kronecker.coordinates k c)) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem ofArrows_e₀ (f : Fin 2 → (X ⟶ Y)) :
    ofArrows k f (Kronecker.e₀ k) = End.of (biprod.fst ≫ biprod.inl) := by
  change fromCoordinates k f ((Kronecker.coordinates k).symm (Kronecker.e₀ k)) = _
  rw [Kronecker.coordinates_symm_e₀]
  apply End.ext
  simp [fromCoordinates, Biprod.ofComponents]

@[simp] theorem ofArrows_e₁ (f : Fin 2 → (X ⟶ Y)) :
    ofArrows k f (Kronecker.e₁ k) = End.of (biprod.snd ≫ biprod.inr) := by
  change fromCoordinates k f ((Kronecker.coordinates k).symm (Kronecker.e₁ k)) = _
  rw [Kronecker.coordinates_symm_e₁]
  apply End.ext
  simp [fromCoordinates, Biprod.ofComponents]

@[simp] theorem ofArrows_arrow (f : Fin 2 → (X ⟶ Y)) (i : Fin 2) :
    ofArrows k f (Kronecker.arrow k i) = End.of (biprod.fst ≫ f i ≫ biprod.inr) := by
  change fromCoordinates k f ((Kronecker.coordinates k).symm (Kronecker.arrow k i)) = _
  rw [Kronecker.coordinates_symm_arrow]
  apply End.ext
  fin_cases i <;> simp [fromCoordinates, Biprod.ofComponents]

/-- Read the diagonal scalars and the two coefficients of the forward block. -/
def toCoordinates (e₀ : (X ⟶ X) ≃ₗ[k] k) (e₁ : (Y ⟶ Y) ≃ₗ[k] k)
    (b : Module.Basis (Fin 2) k (X ⟶ Y)) : End (X ⊞ Y) →ₗ[k] (Fin 4 → k) where
  toFun a := ![e₀ (biprod.inl ≫ a.asHom ≫ biprod.fst),
    e₁ (biprod.inr ≫ a.asHom ≫ biprod.snd),
    b.repr (biprod.inl ≫ a.asHom ≫ biprod.snd) 0,
    b.repr (biprod.inl ≫ a.asHom ≫ biprod.snd) 1]
  map_add' a d := by
    ext i
    fin_cases i <;> simp [Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r a := by
    ext i
    fin_cases i <;> simp [Linear.smul_comp, Linear.comp_smul]

omit [HasBinaryBiproducts C] in
/-- Normalizing the identity identifies every diagonal endomorphism with its scalar. -/
theorem scalar_diagonal {Z : C} (e : (Z ⟶ Z) ≃ₗ[k] k) (he : e (𝟙 Z) = 1) (g : Z ⟶ Z) :
    e g • 𝟙 Z = g := by
  apply e.injective
  simp [he]

/-- The four extracted coordinates recover the original coefficient vector. -/
theorem toCoordinates_fromCoordinates (e₀ : (X ⟶ X) ≃ₗ[k] k) (e₁ : (Y ⟶ Y) ≃ₗ[k] k)
    (b : Module.Basis (Fin 2) k (X ⟶ Y)) (h₀ : e₀ (𝟙 X) = 1) (h₁ : e₁ (𝟙 Y) = 1)
    (c : Fin 4 → k) : toCoordinates k e₀ e₁ b (fromCoordinates k b c) = c := by
  ext i
  fin_cases i <;> simp [toCoordinates, fromCoordinates, Biprod.ofComponents,
    Linear.smul_comp, Linear.comp_smul, h₀, h₁]

/-- With zero reverse Hom, the four coordinates recover every endomorphism. -/
theorem fromCoordinates_toCoordinates [Subsingleton (Y ⟶ X)]
    (e₀ : (X ⟶ X) ≃ₗ[k] k) (e₁ : (Y ⟶ Y) ≃ₗ[k] k)
    (b : Module.Basis (Fin 2) k (X ⟶ Y)) (h₀ : e₀ (𝟙 X) = 1) (h₁ : e₁ (𝟙 Y) = 1)
    (a : End (X ⊞ Y)) : fromCoordinates k b (toCoordinates k e₀ e₁ b a) = a := by
  have hb (g : X ⟶ Y) : b.repr g 0 • b 0 + b.repr g 1 • b 1 = g := by
    simpa only [Fin.sum_univ_two] using b.sum_repr g
  have hz : biprod.inr ≫ a.asHom ≫ biprod.fst = 0 := Subsingleton.elim _ _
  apply End.ext
  change Biprod.ofComponents (e₀ (biprod.inl ≫ a.asHom ≫ biprod.fst) • 𝟙 X)
      (b.repr (biprod.inl ≫ a.asHom ≫ biprod.snd) 0 • b 0 +
        b.repr (biprod.inl ≫ a.asHom ≫ biprod.snd) 1 • b 1) 0
      (e₁ (biprod.inr ≫ a.asHom ≫ biprod.snd) • 𝟙 Y) = a.asHom
  rw [scalar_diagonal k e₀ h₀, scalar_diagonal k e₁ h₁, hb, ← hz]
  exact Biprod.ofComponents_eq a.asHom

/-- A pair with scalar diagonals, no reverse Hom, and two forward basis morphisms
has exactly the concrete Kronecker endomorphism algebra. -/
def linearEquiv [Subsingleton (Y ⟶ X)]
    (e₀ : (X ⟶ X) ≃ₗ[k] k) (e₁ : (Y ⟶ Y) ≃ₗ[k] k)
    (b : Module.Basis (Fin 2) k (X ⟶ Y)) (h₀ : e₀ (𝟙 X) = 1) (h₁ : e₁ (𝟙 Y) = 1) :
    Kronecker.Algebra k ≃ₗ[k] End (X ⊞ Y) where
  toFun := ofArrows k b
  map_add' := (ofArrows k b).map_add
  map_smul' := (ofArrows k b).toLinearMap.map_smul'
  invFun a := Kronecker.coordinates k (toCoordinates k e₀ e₁ b a)
  left_inv a := by
    obtain ⟨c, rfl⟩ := (Kronecker.coordinates k).surjective a
    change Kronecker.coordinates k
      (toCoordinates k e₀ e₁ b (ofArrows k b (Kronecker.coordinates k c))) = _
    rw [ofArrows_coordinates, toCoordinates_fromCoordinates k e₀ e₁ b h₀ h₁]
  right_inv a := by
    change ofArrows k b (Kronecker.coordinates k (toCoordinates k e₀ e₁ b a)) = a
    rw [ofArrows_coordinates]
    exact fromCoordinates_toCoordinates k e₀ e₁ b h₀ h₁ a

/-- The categorical endomorphism algebra of the pair is the Kronecker algebra. -/
def algebraEquiv [Subsingleton (Y ⟶ X)]
    (e₀ : (X ⟶ X) ≃ₗ[k] k) (e₁ : (Y ⟶ Y) ≃ₗ[k] k)
    (b : Module.Basis (Fin 2) k (X ⟶ Y)) (h₀ : e₀ (𝟙 X) = 1) (h₁ : e₁ (𝟙 Y) = 1) :
    Kronecker.Algebra k ≃ₐ[k] End (X ⊞ Y) :=
  AlgEquiv.ofLinearEquiv (linearEquiv k e₀ e₁ b h₀ h₁)
    (ofArrows k b).map_one (ofArrows k b).map_mul

@[simp] theorem algebraEquiv_apply [Subsingleton (Y ⟶ X)]
    (e₀ : (X ⟶ X) ≃ₗ[k] k) (e₁ : (Y ⟶ Y) ≃ₗ[k] k)
    (b : Module.Basis (Fin 2) k (X ⟶ Y)) (h₀ : e₀ (𝟙 X) = 1) (h₁ : e₁ (𝟙 Y) = 1)
    (a : Kronecker.Algebra k) : algebraEquiv k e₀ e₁ b h₀ h₁ a = ofArrows k b a := rfl

/-- In particular, the endomorphism algebra of such a pair is finite dimensional. -/
theorem finiteDimensional [Subsingleton (Y ⟶ X)]
    (e₀ : (X ⟶ X) ≃ₗ[k] k) (e₁ : (Y ⟶ Y) ≃ₗ[k] k)
    (b : Module.Basis (Fin 2) k (X ⟶ Y)) (h₀ : e₀ (𝟙 X) = 1) (h₁ : e₁ (𝟙 Y) = 1) :
    FiniteDimensional k (End (X ⊞ Y)) :=
  (linearEquiv k e₀ e₁ b h₀ h₁).finiteDimensional

/-- The complete endomorphism algebra has dimension four. -/
theorem finrank [Subsingleton (Y ⟶ X)]
    (e₀ : (X ⟶ X) ≃ₗ[k] k) (e₁ : (Y ⟶ Y) ≃ₗ[k] k)
    (b : Module.Basis (Fin 2) k (X ⟶ Y)) (h₀ : e₀ (𝟙 X) = 1) (h₁ : e₁ (𝟙 Y) = 1) :
    Module.finrank k (End (X ⊞ Y)) = 4 :=
  (linearEquiv k e₀ e₁ b h₀ h₁).finrank_eq.symm.trans (Kronecker.finrank k)


end Beilinson.KroneckerEnd

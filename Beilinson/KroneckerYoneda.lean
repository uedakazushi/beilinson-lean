module

public import Beilinson.KroneckerEnd
public import Beilinson.KroneckerModule

/-! Precomposition by the two arrows gives the reverse-arrow action on Hom.
This identifies the right-action convention used by the tilting functor. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Beilinson.KroneckerYoneda

universe u v w

variable (k : Type u) [Field k] {C : Type w} [Category.{v} C]
  [Preadditive C] [Linear k C] [HasBinaryBiproducts C] {X Y Z : C}

/-- Restrict a morphism to the two summands. -/
def homCoordinates : ((X ⊞ Y) ⟶ Z) ≃ₗ[k] ((X ⟶ Z) × (Y ⟶ Z)) where
  toFun h := (biprod.inl ≫ h, biprod.inr ≫ h)
  invFun h := biprod.desc h.1 h.2
  left_inv h := by
    apply biprod.hom_ext' <;> simp
  right_inv h := by simp
  map_add' h g := by simp [Preadditive.comp_add]
  map_smul' r h := by simp [Linear.comp_smul]

/-- The decomposition is natural in the target of Hom. -/
theorem homCoordinates_postcompose {W : C} (h : (X ⊞ Y) ⟶ Z) (g : Z ⟶ W) :
    homCoordinates k (h ≫ g) =
      ((homCoordinates k h).1 ≫ g, (homCoordinates k h).2 ≫ g) := by
  simp [homCoordinates, Category.assoc]

/-- Contravariance turns the forward geometric arrows into reverse linear maps. -/
def reverseArrows (f : Fin 2 → (X ⟶ Y)) (i : Fin 2) : (Y ⟶ Z) →ₗ[k] (X ⟶ Z) where
  toFun h := f i ≫ h
  map_add' h g := by simp [Preadditive.comp_add]
  map_smul' r h := by simp [Linear.comp_smul]

/-- The Hom decomposition intertwines precomposition with the right Kronecker action. -/
theorem homCoordinates_precompose (f : Fin 2 → (X ⟶ Y))
    (a : Kronecker.Algebra k) (h : (X ⊞ Y) ⟶ Z) :
    homCoordinates k ((KroneckerEnd.ofArrows k f a).asHom ≫ h) =
      Kronecker.ofArrows (reverseArrows k f) (MulOpposite.op a) (homCoordinates k h) := by
  obtain ⟨c, rfl⟩ := (Kronecker.coordinates k).surjective a
  simp only [KroneckerEnd.ofArrows_coordinates]
  change homCoordinates k ((KroneckerEnd.fromCoordinates k f c).asHom ≫ h) =
    Kronecker.actionOfArrows (reverseArrows k f) (Kronecker.coordinates k c)
      (homCoordinates k h)
  rw [Kronecker.actionOfArrows_coordinates]
  ext <;> simp [homCoordinates, KroneckerEnd.fromCoordinates, Biprod.ofComponents,
    reverseArrows, Preadditive.add_comp, Preadditive.comp_add,
    Linear.smul_comp, Linear.comp_smul, Category.assoc, add_assoc]

end Beilinson.KroneckerYoneda

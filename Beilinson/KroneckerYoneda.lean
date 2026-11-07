module

public import Beilinson.KroneckerEnd
public import Beilinson.KroneckerCategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

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

/-- The ordinary Hom functor with its standard right End action restricted to Kronecker. -/
def homFunctor (f : Fin 2 → (X ⟶ Y)) : C ⥤ ModuleCat.{v} (Kronecker.Algebra k)ᵐᵒᵖ :=
  preadditiveCoyonedaObj (X ⊞ Y) ⋙
    ModuleCat.restrictScalars (RingHom.op (KroneckerEnd.ofArrows k f).toRingHom)

/-- Hom with the two summands, viewed as a reverse-quiver representation. -/
def representationFunctor (f : Fin 2 → (X ⟶ Y)) : C ⥤ Kronecker.ReverseRep.{u,v} k where
  obj Z :=
    { V₀ := ModuleCat.of k (X ⟶ Z)
      V₁ := ModuleCat.of k (Y ⟶ Z)
      arrow := reverseArrows k f }
  map g :=
    { zero :=
        { toFun := fun h => h ≫ g
          map_add' := by intros; simp [Preadditive.add_comp]
          map_smul' := by intros; simp [Linear.smul_comp] }
      one :=
        { toFun := fun h => h ≫ g
          map_add' := by intros; simp [Preadditive.add_comp]
          map_smul' := by intros; simp [Linear.smul_comp] }
      comm i := by ext h; exact Category.assoc _ _ _ }
  map_id Z := by
    apply Kronecker.ReverseRep.hom_ext <;> ext h <;> exact Category.comp_id h
  map_comp g h := by
    apply Kronecker.ReverseRep.hom_ext <;> ext m <;> exact (Category.assoc m g h).symm

/-- The Hom decomposition is an isomorphism of actual ordinary right modules. -/
def homModuleEquiv (f : Fin 2 → (X ⟶ Y)) (Z : C) :
    (homFunctor k f).obj Z ≃ₗ[(Kronecker.Algebra k)ᵐᵒᵖ]
      Kronecker.fromReverseRep.obj ((representationFunctor k f).obj Z) where
  toEquiv := (homCoordinates k).toEquiv
  map_add' := (homCoordinates k).map_add
  map_smul' a h := homCoordinates_precompose k f a.unop h

/-- The module identification is natural in the target of Hom. -/
def homFunctorIso (f : Fin 2 → (X ⟶ Y)) :
    homFunctor k f ≅ representationFunctor k f ⋙ Kronecker.fromReverseRep :=
  NatIso.ofComponents (fun Z => (homModuleEquiv k f Z).toModuleIso) (by
    intro Z W g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    exact homCoordinates_postcompose k h g)

end Beilinson.KroneckerYoneda

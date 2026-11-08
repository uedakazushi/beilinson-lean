module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Homology.Additive

/-! Hom cochains out of a complex concentrated in degree zero are the ordinary
Hom spaces into the target terms. The identification respects the differential
and degree-zero precomposition, hence the right endomorphism action. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace Beilinson.CochainFromZero

universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable (P : CochainComplex C ℤ) {E : C} (e : P.X 0 ≅ E)
variable (hP : ∀ i : ℤ, i ≠ 0 → IsZero (P.X i))

/-- Evaluate the source-degree-zero component, using the chosen identification with E. -/
def equiv (I : CochainComplex C ℤ) (n : ℤ) : Cochain P I n ≃ₗ[k] (E ⟶ I.X n) where
  toFun z := e.inv ≫ z.v 0 n (zero_add n)
  invFun f := Cochain.single (e.hom ≫ f) n
  left_inv z := by
    apply Cochain.ext
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      obtain rfl : q = n := by omega
      simp only [Cochain.single_v, Iso.hom_inv_id_assoc]
    · exact (hP p hp).eq_of_src _ _
  right_inv f := by simp only [Cochain.single_v, Iso.inv_hom_id_assoc]
  map_add' _ _ := by simp only [Cochain.add_v, Preadditive.comp_add]
  map_smul' _ _ := by simp only [Cochain.smul_v, Linear.comp_smul, RingHom.id_apply]

/-- Evaluation is natural with respect to maps of target complexes. -/
theorem postcompose {I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ) (z : Cochain P I n) :
    equiv k P e hP J n (z.comp (Cochain.ofHom f) (add_zero n)) =
      equiv k P e hP I n z ≫ f.f n := by
  change e.inv ≫ (z.comp (Cochain.ofHom f) (add_zero n)).v 0 n (zero_add n) =
    (e.inv ≫ z.v 0 n (zero_add n)) ≫ f.f n
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  simp only [Category.assoc]

/-- Degree-zero precomposition is the ordinary right End action on Hom. -/
theorem precompose (I : CochainComplex C ℤ) (n : ℤ)
    (a : Cochain P P 0) (z : Cochain P I n) :
    equiv k P e hP I n (a.comp z (zero_add n)) =
      (e.inv ≫ a.v 0 0 (add_zero 0) ≫ e.hom) ≫ equiv k P e hP I n z := by
  change e.inv ≫ (a.comp z (zero_add n)).v 0 n (zero_add n) =
    (e.inv ≫ a.v 0 0 (add_zero 0) ≫ e.hom) ≫ (e.inv ≫ z.v 0 n (zero_add n))
  rw [Cochain.zero_cochain_comp_v]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The cochain differential becomes postcomposition with the target differential. -/
theorem differential (I : CochainComplex C ℤ) (n : ℤ) (z : Cochain P I n) :
    equiv k P e hP I (n + 1) (δ n (n + 1) z) =
      equiv k P e hP I n z ≫ I.d n (n + 1) := by
  change e.inv ≫ (δ n (n + 1) z).v 0 (n + 1) (zero_add _) =
    (e.inv ≫ z.v 0 n (zero_add n)) ≫ I.d n (n + 1)
  rw [δ_v n (n + 1) rfl z 0 (n + 1) (zero_add _) n 1 (by omega) (by omega)]
  have hd : P.d 0 1 = 0 := (hP 1 one_ne_zero).eq_of_tgt _ _
  simp only [hd, zero_comp, smul_zero, add_zero, Category.assoc]

/-- The Hom complex from a degree-zero source is the termwise ordinary Hom complex. -/
def complexIso (I : CochainComplex C ℤ) :
    CochainComplex.linearHomComplex k P I ≅
      (((linearCoyoneda k C).obj (Opposite.op E)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (equiv k P e hP I n).toModuleIso) (by
      intro i j hij
      obtain rfl : j = i + 1 := hij.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (differential k P e hP I i z).symm)

/-- Hom cochains as a functor; the comparison transports ordinary postcomposition. -/
def functor : CochainComplex C ℤ ⥤ CochainComplex (ModuleCat k) ℤ where
  obj I := CochainComplex.linearHomComplex k P I
  map {I J} f := (complexIso k P e hP I).hom ≫
    (((linearCoyoneda k C).obj (Opposite.op E)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f ≫ (complexIso k P e hP J).inv
  map_id I := by simp
  map_comp f g := by simp

/-- Evaluation gives a natural isomorphism of complexes, not just degreewise bijections. -/
def functorIso : functor k P e hP ≅
    ((linearCoyoneda k C).obj (Opposite.op E)).mapHomologicalComplex
      (ComplexShape.up ℤ) :=
  NatIso.ofComponents (complexIso k P e hP) (by intros; simp [functor])

/-- The transported functor really acts by postcomposition on Hom cochains. -/
theorem functor_map_apply {I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ)
    (z : Cochain P I n) :
    (((functor k P e hP).map f).f n).hom z =
      z.comp (Cochain.ofHom f) (add_zero n) := by
  apply (equiv k P e hP J n).injective
  change equiv k P e hP J n
    ((equiv k P e hP J n).symm (equiv k P e hP I n z ≫ f.f n)) = _
  rw [LinearEquiv.apply_symm_apply, postcompose]

end Beilinson.CochainFromZero

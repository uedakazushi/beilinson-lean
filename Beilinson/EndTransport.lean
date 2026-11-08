module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.FinCases

/-! Transport endomorphism algebras along object isomorphisms and fully faithful
linear functors. The multiplication convention is mathlib's categorical End. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Beilinson.EndTransport

universe u v w v' w'
variable (k : Type u) [CommSemiring k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type w'} [Category.{v'} D] [Preadditive D] [Linear k D]

/-- A two-element biproduct is the binary biproduct, with the indicated order. -/
def pairIso (F : Fin 2 → C) [HasBiproduct F] [HasBinaryBiproduct (F 0) (F 1)] :
    (⨁ F) ≅ F 0 ⊞ F 1 where
  hom := biproduct.desc (Fin.cases (biprod.inl : F 0 ⟶ F 0 ⊞ F 1)
    (Fin.cases (biprod.inr : F 1 ⟶ F 0 ⊞ F 1) (fun i => Fin.elim0 i)))
  inv := biprod.desc (biproduct.ι F 0) (biproduct.ι F 1)
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    fin_cases i <;> simp [Fin.cases, Fin.induction, Fin.induction.go]
  inv_hom_id := by
    apply biprod.hom_ext' <;> simp [Fin.cases, Fin.induction, Fin.induction.go]

/-- Conjugation by an object isomorphism is an algebra equivalence. -/
def iso {X Y : C} (e : X ≅ Y) : End X ≃ₐ[k] End Y :=
  { e.conj with
    map_add' := fun a b => by
      apply End.ext
      change e.inv ≫ (a.asHom + b.asHom) ≫ e.hom = _
      simp only [Preadditive.add_comp, Preadditive.comp_add]
      rfl
    commutes' := fun r => by
      apply End.ext
      change e.inv ≫ (r • 𝟙 X) ≫ e.hom = r • 𝟙 Y
      simp [Linear.smul_comp, Linear.comp_smul] }

/-- A linear functor acts by an algebra homomorphism on endomorphisms. -/
def map (F : C ⥤ D) [F.Additive] [F.Linear k] (X : C) : End X →ₐ[k] End (F.obj X) :=
  { F.mapEnd (X := X) with
    map_add' := fun a b => End.ext (F.map_add)
    map_zero' := End.ext (F.map_zero _ _)
    commutes' := fun r => by
      apply End.ext
      change F.map (r • 𝟙 X) = r • 𝟙 (F.obj X)
      rw [Functor.map_smul, F.map_id] }

/-- Full faithfulness makes the preceding algebra homomorphism invertible. -/
def mapEquiv (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful] (X : C) :
    End X ≃ₐ[k] End (F.obj X) :=
  AlgEquiv.ofBijective (map k F X) (by
    constructor
    · intro a b h
      exact End.ext (F.map_injective (congrArg End.asHom h))
    · intro g
      obtain ⟨f, hf⟩ := F.map_surjective g.asHom
      exact ⟨End.of f, End.ext hf⟩)

end Beilinson.EndTransport

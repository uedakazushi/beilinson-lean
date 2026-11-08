module

public import Beilinson.EndTransport
public import SheafHomSections
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Derived
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEquivalenceLinear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.Data.Fin.Rev

/-! The canonical geometric comparison of the negative and positive twist windows.
It uses twisting and reindexing, without choosing bases of Hom spaces. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open Stacks.AlgebraicGeometry.ExampleGenerator (twistModule twistFamily twistSumModule)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Beilinson.PositiveWindow

universe u

private theorem rightTensorLinear {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (L : X.Modules) :
    letI : Linear R X.Modules := modulesLinear R (Over.mk f)
    (show X.Modules ⥤ X.Modules from
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf).flip.obj L).Linear R := by
  let : Linear R X.Modules := modulesLinear R (Over.mk f)
  exact (SheafHomSections.linearOver_eq_modulesLinear f) ▸
    SheafHomSections.tensorRightLinear f L

variable (k : Type u) [CommRing k] (n : ℕ)

local instance baseLinear : Linear k (AlgebraicGeometry.Proj (polyGrading k n)).Modules :=
  Stacks.AlgebraicGeometry.Beilinson.projectiveSpaceModulesLinear k n
local instance finiteBiproducts : HasFiniteBiproducts
    (AlgebraicGeometry.Proj (polyGrading k n)).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The positive family O(0), …, O(n), with the book's ordering. -/
def positiveFamily : Fin (n + 1) → (AlgebraicGeometry.Proj (polyGrading k n)).Modules :=
  fun i => twistModule k n (i : ℤ)

def positiveGenerator : (AlgebraicGeometry.Proj (polyGrading k n)).Modules :=
  ⨁ positiveFamily k n

/-- Twisting is linear for the same scalar structure as the geometric equivalence. -/
theorem twist_linear (d : ℤ) : (twistModules k n d).Linear k := by
  let F : (AlgebraicGeometry.Proj (polyGrading k n)).Modules ⥤
      (AlgebraicGeometry.Proj (polyGrading k n)).Modules :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u}
      (AlgebraicGeometry.Proj (polyGrading k n)).sheaf).flip.obj (twistModule k n d)
  have hF : F.Linear k := rightTensorLinear (projToSpecCoeff k n) (twistModule k n d)
  rw [Functor.linear_iff]
  intro M a
  exact (Functor.linear_iff k F).mp hF M a

/-- Each negative summand, twisted by n, is the corresponding reversed positive summand. -/
def componentIso (i : Fin (n + 1)) :
    (twistModules k n (n : ℤ)).obj (twistFamily k n i) ≅ positiveFamily k n i.rev :=
  twistModulesTwistingSheafIso k n (-(i : ℤ)) (n : ℤ) ≪≫
    eqToIso (congrArg (twistModule k n) (by
      have hi := i.isLt
      change -(i : ℤ) + (n : ℤ) = ((i.rev).val : ℤ)
      rw [Fin.val_rev]
      omega))

/-- The actual geometric isomorphism E(n) ≅ O ⊕ O(1) ⊕ … ⊕ O(n). -/
def generatorIso :
    (twistModules k n (n : ℤ)).obj (twistSumModule k n) ≅ positiveGenerator k n :=
  (twistModules k n (n : ℤ)).mapBiproduct (twistFamily k n) ≪≫
    biproduct.mapIso (componentIso k n) ≪≫
      biproduct.reindex (Fin.revPerm (n := n + 1)) (positiveFamily k n)

/-- Canonical transport of End(E) to the positive-window End, via twisting. -/
def endAlgebraEquiv : End (twistSumModule k n) ≃ₐ[k] End (positiveGenerator k n) := by
  let : (twistModules k n (n : ℤ)).Linear k := twist_linear k n (n : ℤ)
  exact (EndTransport.mapEquiv k (twistModules k n (n : ℤ)) (twistSumModule k n)).trans
    (EndTransport.iso k (generatorIso k n))

def endRingEquiv : End (twistSumModule k n) ≃+* End (positiveGenerator k n) :=
  (endAlgebraEquiv k n).toRingEquiv

#print axioms Beilinson.PositiveWindow.twist_linear
#print axioms Beilinson.PositiveWindow.generatorIso
#print axioms Beilinson.PositiveWindow.endAlgebraEquiv

end Beilinson.PositiveWindow

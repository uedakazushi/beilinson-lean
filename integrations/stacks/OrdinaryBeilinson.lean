module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEquivalenceLinear
public import ConcentratedDGA
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects.ThickSubcategory

/-! The unbounded ordinary-right-module form of the negative-window Beilinson
functor. The ordinary ring is the underlying ring of the geometric endomorphism
dg algebra, explicitly identified upstream with End(O ⊕ O(-1) ⊕ … ⊕ O(-n)).
The bounded coherent restriction and positive-window identification are separate.

The base ring of that dg algebra is ℤ, and the degree-zero comparison has equal
base/module universes. This first geometric application is therefore at universe zero. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.Beilinson
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

attribute [local instance] isClosedUnderIsomorphisms_isCompactObject

namespace Beilinson.OrdinaryBeilinson

local instance moduleDerivedCategory (R : Type) [Ring R] :
    HasDerivedCategory (ModuleCat.{0} R) := HasDerivedCategory.standard _

/-- The concentrated geometric dg algebra, compared with ordinary right modules. -/
def ordinaryComparison (A : Type) [CommRing A] (n : ℕ) :
    ConcentratedDGA.Comparison (endAlgebra A n) :=
  ConcentratedDGA.comparison (endAlgebra A n)
    (endAlgebra_mem_grading_zero A n)
    (fun m hm => endAlgebra_grading_eq_bot A n hm)
    (fun x => by rw [endAlgebra_d_eq_zero]; rfl)

/-- Ordinary right modules over the underlying geometric endomorphism ring. -/
abbrev ordinaryDerivedCategory (A : Type) [CommRing A] (n : ℕ) :=
  DerivedCategory (ModuleCat.{0} (endAlgebra A n).Aᵐᵒᵖ)

/-- Convert an ordinary complex to a dg module, then tensor with the negative twist sum. -/
def ordinaryTensor (A : Type) [CommRing A] (n : ℕ) :
    ordinaryDerivedCategory A n ⥤
      Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
  (ordinaryComparison A n).equivalence.inverse ⋙ tensorWithGenerator A n

instance ordinaryTensor_isEquivalence (A : Type) [CommRing A] (n : ℕ) :
    (ordinaryTensor A n).IsEquivalence := by
  let : (tensorWithGenerator A n).IsEquivalence := tensorWithGenerator_isEquivalence A n
  dsimp only [ordinaryTensor]
  infer_instance

instance ordinaryComparison_commShift (A : Type) [CommRing A] (n : ℕ) :
    (ordinaryComparison A n).equivalence.functor.CommShift ℤ :=
  (ordinaryComparison A n).commShift

instance ordinaryComparison_inverseCommShift (A : Type) [CommRing A] (n : ℕ) :
    (ordinaryComparison A n).equivalence.inverse.CommShift ℤ :=
  (ordinaryComparison A n).inverseCommShift

instance ordinaryComparison_inverseIsTriangulated (A : Type) [CommRing A] (n : ℕ) :
    (ordinaryComparison A n).equivalence.inverse.IsTriangulated :=
  (ordinaryComparison A n).inverse_isTriangulated

instance ordinaryTensor_commShift (A : Type) [CommRing A] (n : ℕ) :
    (ordinaryTensor A n).CommShift ℤ :=
  inferInstanceAs (((ordinaryComparison A n).equivalence.inverse ⋙
    tensorWithGenerator A n).CommShift ℤ)

instance ordinaryTensor_isTriangulated (A : Type) [CommRing A] (n : ℕ) :
    (ordinaryTensor A n).IsTriangulated := by
  let : (tensorWithGenerator A n).IsTriangulated := tensorWithGenerator_isTriangulated A n
  change ((ordinaryComparison A n).equivalence.inverse ⋙ tensorWithGenerator A n).IsTriangulated
  infer_instance

/-- The unbounded geometric equivalence with an ordinary right-module source. -/
def equivalence (A : Type) [CommRing A] (n : ℕ) :
    ordinaryDerivedCategory A n ≌
      Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
  (ordinaryTensor A n).asEquivalence

/-- The derived category of actual ordinary right End(E)-modules. -/
abbrev endDerivedCategory (A : Type) [CommRing A] (n : ℕ) :=
  DerivedCategory (ModuleCat.{0}
    (CategoryTheory.End (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumModule A n))ᵐᵒᵖ)

/-- Restrict along the explicit identification of the geometric dg ring with End(E). -/
abbrev restrictEnd (A : Type) [CommRing A] (n : ℕ) :
    ModuleCat.{0}
        (CategoryTheory.End (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumModule A n))ᵐᵒᵖ ⥤
      ModuleCat.{0} (endAlgebra A n).Aᵐᵒᵖ :=
  ModuleCat.restrictScalars (RingEquiv.op (endAlgebraRingEquiv A n)).toRingHom

instance restrictEnd_isEquivalence (A : Type) [CommRing A] (n : ℕ) :
    (restrictEnd A n).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv _

/-- Tensor with E, with the source written as ordinary right End(E)-modules. -/
def endTensor (A : Type) [CommRing A] (n : ℕ) :
    endDerivedCategory A n ⥤
      Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
  (restrictEnd A n).mapDerivedCategory ⋙ ordinaryTensor A n

instance endTensor_isEquivalence (A : Type) [CommRing A] (n : ℕ) :
    (endTensor A n).IsEquivalence := by
  let G := restrictEnd A n
  let : G.mapDerivedCategory.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence G
  dsimp only [endTensor]
  infer_instance

instance endTensor_commShift (A : Type) [CommRing A] (n : ℕ) :
    (endTensor A n).CommShift ℤ :=
  inferInstanceAs (((restrictEnd A n).mapDerivedCategory ⋙ ordinaryTensor A n).CommShift ℤ)

instance endTensor_isTriangulated (A : Type) [CommRing A] (n : ℕ) :
    (endTensor A n).IsTriangulated := by
  change ((restrictEnd A n).mapDerivedCategory ⋙ ordinaryTensor A n).IsTriangulated
  infer_instance

/-- The ordinary, unbounded negative-window Beilinson equivalence. -/
def endEquivalence (A : Type) [CommRing A] (n : ℕ) :
    endDerivedCategory A n ≌
      Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
  (endTensor A n).asEquivalence

instance endEquivalence_commShift (A : Type) [CommRing A] (n : ℕ) :
    (endEquivalence A n).functor.CommShift ℤ :=
  inferInstanceAs ((endTensor A n).CommShift ℤ)

instance endEquivalence_isTriangulated (A : Type) [CommRing A] (n : ℕ) :
    (endEquivalence A n).functor.IsTriangulated :=
  inferInstanceAs ((endTensor A n).IsTriangulated)

/-- The same functor restricts to compact objects; no geometric regularity is assumed. -/
def compactEndEquivalence (A : Type) [CommRing A] (n : ℕ) :
    ObjectProperty.FullSubcategory (IsCompactObject.{0} (C := endDerivedCategory A n)) ≌
      ObjectProperty.FullSubcategory (IsCompactObject.{0} (C :=
        Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)))) :=
  (endEquivalence A n).congrFullSubcategory (by
    funext K
    apply propext
    exact (isCompactObject_iff_isCompactObject_obj (endTensor A n) K).symm)

#print axioms Beilinson.OrdinaryBeilinson.compactEndEquivalence
#print axioms Beilinson.OrdinaryBeilinson.endTensor_isTriangulated
#print axioms Beilinson.OrdinaryBeilinson.endEquivalence
#print axioms Beilinson.OrdinaryBeilinson.ordinaryComparison
#print axioms Beilinson.OrdinaryBeilinson.ordinaryTensor_isTriangulated
#print axioms Beilinson.OrdinaryBeilinson.equivalence

end Beilinson.OrdinaryBeilinson

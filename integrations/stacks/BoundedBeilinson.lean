module

public import OrdinaryBeilinson
public import ProjectivePerfectProbe
public import CoherentDerivedComparison

/-! A bounded-coherent restriction of the ordinary-module Beilinson functor.
The source is compact right End(E)-module objects; identifying it with the bounded
derived category of finite-dimensional modules is a separate remaining step.
The target is compared explicitly with D^b(Coh) itself. -/

set_option autoImplicit false

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
attribute [local instance] isClosedUnderIsomorphisms_isCompactObject
  isTriangulated_isCompactObject

namespace Beilinson.BoundedBeilinson

local instance moduleDerivedCategory (R : Type) [Ring R] :
    HasDerivedCategory (ModuleCat.{0} R) := HasDerivedCategory.standard _

/-- Bounded coherent cohomology, regarded as a property of D_QCoh objects. -/
abbrev boundedCoherent (k : Type) [Field k] (n : ℕ) :
    ObjectProperty (Stacks.Duality.quasiCoherentDerivedCategory
      (AlgebraicGeometry.Proj (polyGrading k n))) :=
  fun K => DerivedCategoryB.derivedCategoryBBounded
    (fun M : (AlgebraicGeometry.Proj (polyGrading k n)).Modules => M.IsCoherent) K.obj

theorem boundedCoherent_eq_compact (k : Type) [Field k] (n : ℕ) :
    boundedCoherent k n = IsCompactObject.{0} := by
  funext K
  exact propext (ProjectivePerfectProbe.compact_iff_boundedCoherent k n K).symm

instance boundedCoherent_closed (k : Type) [Field k] (n : ℕ) :
    (boundedCoherent k n).IsClosedUnderIsomorphisms := by
  rw [boundedCoherent_eq_compact]
  infer_instance

instance boundedCoherent_triangulated (k : Type) [Field k] (n : ℕ) :
    (boundedCoherent k n).IsTriangulated := by
  rw [boundedCoherent_eq_compact]
  infer_instance

/-- The unbounded ordinary tensor functor restricts exactly to bounded coherent targets. -/
def equivalence (k : Type) [Field k] (n : ℕ) :
    ObjectProperty.FullSubcategory
        (IsCompactObject.{0} (C := OrdinaryBeilinson.endDerivedCategory k n)) ≌
      (boundedCoherent k n).FullSubcategory :=
  (OrdinaryBeilinson.endEquivalence k n).congrFullSubcategory (by
    funext K
    apply propext
    change boundedCoherent k n ((OrdinaryBeilinson.endTensor k n).obj K) ↔ _
    exact (ProjectivePerfectProbe.compact_iff_boundedCoherent k n _).symm.trans
      (isCompactObject_iff_isCompactObject_obj (OrdinaryBeilinson.endTensor k n) K).symm)

instance equivalence_commShift (k : Type) [Field k] (n : ℕ) :
    (equivalence k n).functor.CommShift ℤ := by
  dsimp only [equivalence, Equivalence.congrFullSubcategory]
  infer_instance

instance equivalence_isTriangulated (k : Type) [Field k] (n : ℕ) :
    (equivalence k n).functor.IsTriangulated := by
  dsimp only [equivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- The target is the actual bounded derived category of coherent sheaves. -/
def coherentEquivalence (k : Type) [Field k] (n : ℕ) :=
  (equivalence k n).trans
    (CoherentDerivedComparison.equivalence (AlgebraicGeometry.Proj (polyGrading k n))).symm

instance coherentEquivalence_commShift (k : Type) [Field k] (n : ℕ) :
    (coherentEquivalence k n).functor.CommShift ℤ := by
  change ((equivalence k n).functor ⋙
    (CoherentDerivedComparison.equivalence (AlgebraicGeometry.Proj (polyGrading k n))).inverse).CommShift ℤ
  infer_instance

instance coherentEquivalence_isTriangulated (k : Type) [Field k] (n : ℕ) :
    (coherentEquivalence k n).functor.IsTriangulated := by
  change ((equivalence k n).functor ⋙
    (CoherentDerivedComparison.equivalence (AlgebraicGeometry.Proj (polyGrading k n))).inverse).IsTriangulated
  infer_instance

instance coherentEquivalence_inverseCommShift (k : Type) [Field k] (n : ℕ) :
    (coherentEquivalence k n).inverse.CommShift ℤ :=
  (coherentEquivalence k n).commShiftInverse ℤ

instance coherentEquivalence_inverseIsTriangulated (k : Type) [Field k] (n : ℕ) :
    (coherentEquivalence k n).inverse.IsTriangulated := by
  let E := coherentEquivalence k n
  let : E.toAdjunction.CommShift ℤ := E.toAdjunction.commShift_of_leftAdjoint ℤ
  exact E.toAdjunction.isTriangulated_rightAdjoint

#print axioms Beilinson.BoundedBeilinson.coherentEquivalence_inverseIsTriangulated
#print axioms Beilinson.BoundedBeilinson.coherentEquivalence_isTriangulated
#print axioms Beilinson.BoundedBeilinson.coherentEquivalence
#print axioms Beilinson.BoundedBeilinson.equivalence_isTriangulated
#print axioms Beilinson.BoundedBeilinson.boundedCoherent_eq_compact
#print axioms Beilinson.BoundedBeilinson.equivalence

end Beilinson.BoundedBeilinson

module

public import Beilinson.AdjunctionLift
public import GeometricEndHom

/-! Identify the inverse of the existing ordinary negative-window equivalence
with the independently defined classical RHom, after explicit model change. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.Beilinson
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] SheafOfModules.hasDerivedCategory Scheme.Modules.hasDerivedCategory

namespace Beilinson.NegativeDerivedHom

variable (A : Type) [CommRing A] (n : ℕ)

local instance moduleDerivedCategory (R : Type) [Ring R] :
    HasDerivedCategory (ModuleCat.{0} R) := HasDerivedCategory.standard _

/-- The actual quasi-coherent inclusion into the geometric derived-category model. -/
def inclusion :=
  (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf)).ι

/-- The ambient tensor-Hom adjunction, with the required shift convention and model change. -/
def ambientAdjunction :=
  (RingedSite.tensorWithComplexDerived_adj_derivedHomWithComplex (site A n) (generator A n)).compSignTwist.comp
    (modelEquivalence A n).toAdjunction

def dgRight : Stacks.Duality.quasiCoherentDerivedCategory
    (AlgebraicGeometry.Proj (polyGrading A n)) ⥤ derivedCategoryR A n :=
  inclusion A n ⋙ (modelEquivalence A n).inverse ⋙
    CategoryTheory.signTwist _ ⋙ RingedSite.derivedHomWithComplex (site A n) (generator A n)

/-- The actual dg tensor restricted to D_QCoh is left adjoint to the restricted RHom. -/
def tensorAdjunction : tensorWithGenerator A n ⊣ dgRight A n :=
  AdjunctionLift.restrictTarget _ (ambientAdjunction A n) (tensorWithGenerator_obj_mem A n)

def ordinaryRight := dgRight A n ⋙ (OrdinaryBeilinson.ordinaryComparison A n).equivalence.functor

def ordinaryAdjunction : OrdinaryBeilinson.ordinaryTensor A n ⊣ ordinaryRight A n :=
  (OrdinaryBeilinson.ordinaryComparison A n).equivalence.symm.toAdjunction.comp
    (tensorAdjunction A n)

/-- The chosen inverse is canonically the right adjoint, by uniqueness of right adjoints. -/
def ordinaryInverseIso : (OrdinaryBeilinson.equivalence A n).inverse ≅ ordinaryRight A n :=
  AdjunctionLift.inverseIso (OrdinaryBeilinson.equivalence A n) _
    (ordinaryAdjunction A n)

/-- Independently derived ordinary Hom, read on D_QCoh in the geometric model. -/
def classicalOrdinary := inclusion A n ⋙ (modelEquivalence A n).inverse ⋙
  GeometricDerivedHom.classicalHom A n

/-- The existing equivalence's inverse agrees naturally with classical RHom. -/
def classicalInverseIso : (OrdinaryBeilinson.equivalence A n).inverse ≅ classicalOrdinary A n :=
  ordinaryInverseIso A n ≪≫
    Functor.isoWhiskerLeft (inclusion A n ⋙ (modelEquivalence A n).inverse)
      (GeometricDerivedHom.derivedIso A n)

#print axioms tensorAdjunction
#print axioms classicalInverseIso

end Beilinson.NegativeDerivedHom

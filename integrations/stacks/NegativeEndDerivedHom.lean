module

public import NegativeDerivedHom
public import DerivedRingEquivalence

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

local instance endModuleDerivedCategory (R : Type) [Ring R] :
    HasDerivedCategory (ModuleCat.{0} R) := HasDerivedCategory.standard _

/-- The actual derived coefficient-change equivalence used by the End(E) tensor functor. -/
def coefficientEquivalence : OrdinaryBeilinson.endDerivedCategory A n ≌
    OrdinaryBeilinson.ordinaryDerivedCategory A n :=
  DerivedRingEquivalence.equivalence (endAlgebraRingEquiv A n)

#print axioms coefficientEquivalence

def endRight := ordinaryRight A n ⋙ (coefficientEquivalence A n).inverse

def endAdjunction : OrdinaryBeilinson.endTensor A n ⊣ endRight A n :=
  (coefficientEquivalence A n).toAdjunction.comp (ordinaryAdjunction A n)

#print axioms endAdjunction

def endInverseIso : (OrdinaryBeilinson.endEquivalence A n).inverse ≅ endRight A n :=
  AdjunctionLift.inverseIso (OrdinaryBeilinson.endEquivalence A n) _
    (endAdjunction A n)

#print axioms endInverseIso

/-- Classical RHom(E,-), with the actual right End(E) target and explicit source model change. -/
def modelInclusion : Stacks.Duality.quasiCoherentDerivedCategory
    (AlgebraicGeometry.Proj (polyGrading A n)) ⥤
      @DerivedCategory (GeometricDerivedHom.C A n) _ _ (HasDerivedCategory.standard _) :=
  inclusion A n ⋙ (modelEquivalence A n).inverse

def classicalEnd := modelInclusion A n ⋙
  GeometricEndHom.classicalEndHom A n

#print axioms classicalEnd

def ordinaryRightEndIso :=
  DerivedRingEquivalence.whiskerComparison (endAlgebraRingEquivTensorModO A n)
    (endModulesRingEquiv A n) (modelInclusion A n) (GeometricEndHom.sourceHom A n)
    (GeometricDerivedHom.dgHom A n) (GeometricDerivedHom.ordinaryDerivedIso A n)

#print axioms ordinaryRightEndIso

/-- The existing actual right-End(E) equivalence has the classical RHom inverse. -/
def classicalEndInverseIso : (OrdinaryBeilinson.endEquivalence A n).inverse ≅ classicalEnd A n :=
  endInverseIso A n ≪≫ AdjunctionLift.cancelRight (coefficientEquivalence A n)
    (ordinaryRight A n) (classicalEnd A n) (ordinaryRightEndIso A n)

#print axioms classicalEndInverseIso

end Beilinson.NegativeDerivedHom

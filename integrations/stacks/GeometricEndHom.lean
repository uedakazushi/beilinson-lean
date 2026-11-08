module

public import GeometricDerivedHom
public import RingChangeDerived

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.Beilinson

attribute [local instance 10000] HasDerivedCategory.standard

namespace Beilinson.GeometricEndHom

variable (A : Type) [CommRing A] (n : ℕ)

local instance : IsGrothendieckAbelian.{0} (GeometricDerivedHom.C A n) :=
  Stacks.SheafOfModules.sheafModulesGrothendieck _ _

/-- Fix the classical source and target before changing coefficient-ring spellings. -/
def sourceHom : DerivedCategory (GeometricDerivedHom.C A n) ⥤
    DerivedCategory (ModuleCat.{0} (End (generatorModule A n))ᵐᵒᵖ) :=
  DerivedHomTransport.derivedHom (generatorModule A n)

/-- Classical RHom with the actual right End(E) target, via the explicit ring identification. -/
def classicalEndHom := RingChangeDerived.postcompose (endModulesRingEquiv A n) (sourceHom A n)

/-- Compare dg RHom with this actual right-End(E)-valued classical Hom. -/
def ordinaryEndIso :=
  RingChangeDerived.liftComparison (endAlgebraRingEquivTensorModO A n) (endModulesRingEquiv A n)
    (sourceHom A n) (GeometricDerivedHom.dgHom A n) (GeometricDerivedHom.ordinaryDerivedIso A n)

#print axioms ordinaryEndIso
#print axioms classicalEndHom
#print axioms sourceHom

end Beilinson.GeometricEndHom

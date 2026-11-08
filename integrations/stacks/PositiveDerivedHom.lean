module

public import DerivedHomTransport
public import PositiveWindow

/-! The positive and negative classical RHom functors on projective space,
independently defined by deriving ordinary right-End-module Hom, agree under
twisting and the canonical coefficient-ring change. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ExampleGenerator (twistSumModule)
open Stacks.AlgebraicGeometry.ProjTwistFunctor (twistModules)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] SheafOfModules.hasDerivedCategory Scheme.Modules.hasDerivedCategory

namespace Beilinson.PositiveDerivedHom

universe u
variable (k : Type u) [CommRing k] (n : ℕ)

local instance : Linear k (AlgebraicGeometry.Proj (polyGrading k n)).Modules :=
  Stacks.AlgebraicGeometry.Beilinson.projectiveSpaceModulesLinear k n

local instance : IsGrothendieckAbelian.{u}
    (AlgebraicGeometry.Proj (polyGrading k n)).Modules :=
  Stacks.SheafOfModules.sheafModulesGrothendieck _ _

local instance moduleDerivedCategory (R : Type u) [Ring R] :
    HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _

/-- Classical RHom(E,-) with ordinary right End(E) coefficients. -/
def negativeHom := DerivedHomTransport.derivedHom (twistSumModule k n)

/-- Classical RHom(T,-) with ordinary right End(T) coefficients. -/
def positiveHom := DerivedHomTransport.derivedHom (PositiveWindow.positiveGenerator k n)

/-- The actual coefficient equivalence, with no choice of a Hom basis. -/
def coefficients :
    ModuleCat.{u} (End (PositiveWindow.positiveGenerator k n))ᵐᵒᵖ ≌
      ModuleCat.{u} (End (twistSumModule k n))ᵐᵒᵖ :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.op (PositiveWindow.endRingEquiv k n))

instance coefficients_inverse_additive : (coefficients k n).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The classical derived Hom comparison, on the actual ambient derived categories. -/
def twistIso : negativeHom k n ⋙ (coefficients k n).inverse.mapDerivedCategory ≅
    (twistModules k n (n : ℤ)).mapDerivedCategory ⋙ positiveHom k n := by
  letI : (twistModules k n (n : ℤ)).Linear k := PositiveWindow.twist_linear k n (n : ℤ)
  exact DerivedHomTransport.derivedIso k (twistModules k n (n : ℤ))
    (twistSumModule k n) (PositiveWindow.generatorIso k n)

#print axioms negativeHom
#print axioms positiveHom
#print axioms twistIso

end Beilinson.PositiveDerivedHom

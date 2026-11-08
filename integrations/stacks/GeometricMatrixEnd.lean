module

public import MatrixAlgebraComparison
public import BoundedBeilinson
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorHomGroups

/-! Identify the compactness model of the Beilinson algebra with the actual
negative-window geometric End ring, in every dimension. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjectiveGenerator
open Stacks.AlgebraicGeometry.ExampleGenerator (twistSumModule)
open StacksDraft.Perfect

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Beilinson.GeometricMatrixEnd

universe u
variable (k : Type u) [Field k] (n : ℕ)

/-- The matrix construction and the dg construction use the same negative twist sum. -/
def generatorIso : projTwistSum k n ≅ twistSumModule k n := Iso.refl _

/-- Keep the explicit additive structures when changing the spelling of the module category. -/
def generatorEndRingEquiv : End (projTwistSum k n) ≃+* End (twistSumModule k n) where
  toEquiv := Equiv.refl _
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The polynomial-matrix algebra is the actual End(E), with composition multiplication. -/
def ringEquiv : beilinsonAlgebra k n ≃+* End (twistSumModule k n) :=
  (MatrixAlgebraComparison.algebraEquiv k n).toRingEquiv |>.trans
    ((matrixRingEquivEnd k n).trans (generatorEndRingEquiv k n))

#print axioms ringEquiv
#print axioms generatorIso

end Beilinson.GeometricMatrixEnd

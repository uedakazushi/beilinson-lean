module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroTriangulated

/-! Ordinary right modules versus dg modules over an algebra in degree zero.
This verifies the opposite-ring convention independently of the geometry. -/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedAlgebra DifferentialGradedModule

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace Beilinson.StacksOrdinaryProbe

universe u v

variable (R : Type u) [CommRing R] (S : Type u) [Ring S] [Algebra R S]
  [HasDerivedCategory.{v} (ModuleCat.{u} Sᵐᵒᵖ)]

/-- A degree-zero dg algebra has the derived category of ordinary right modules. -/
def rightModuleComparison :
    derivedCategory' (degreeZero R S) ≌ DerivedCategory (ModuleCat.{u} Sᵐᵒᵖ) :=
  degreeZeroDerivedEquivalence (R := R) (S := S) (A := Sᵐᵒᵖ)

/-- The comparison admits a shift structure for which it preserves distinguished triangles. -/
theorem rightModuleComparison_exact :
    ∃ h : (rightModuleComparison R S).functor.CommShift ℤ, letI := h;
      (rightModuleComparison R S).functor.IsTriangulated :=
  degreeZeroDerivedEquivalence_functor_exact (R := R) (S := S) (A := Sᵐᵒᵖ)

#print axioms Beilinson.StacksOrdinaryProbe.rightModuleComparison
#print axioms Beilinson.StacksOrdinaryProbe.rightModuleComparison_exact

end Beilinson.StacksOrdinaryProbe

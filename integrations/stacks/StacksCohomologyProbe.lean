module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TwistAcyclicRange

/-! Negative twists on the base-change model of projective space.
This does not identify that model with the polynomial Proj used by the Koszul probe. -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

attribute [local instance 2000] HasDerivedCategory.standard

namespace Beilinson.StacksCohomologyProbe

universe u

/-- Negative twists in the Beilinson band have zero higher direct images in every degree. -/
theorem negative_twist_acyclic (m : ℕ) (S : Scheme.{u}) {d : ℤ}
    (hd₁ : -((m + 1 : ℕ) : ℤ) ≤ d) (hd₂ : d < 0) (q : ℤ) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
      q).obj (twistOver (m + 1) S d)) :=
  Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isZero_rightDerivedPlus_pushforward_twistOver_of_acyclic m S hd₁ hd₂ q

#print axioms Beilinson.StacksCohomologyProbe.negative_twist_acyclic

end Beilinson.StacksCohomologyProbe

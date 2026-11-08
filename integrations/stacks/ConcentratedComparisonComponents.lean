module

public import ConcentratedComponents
public import ConcentratedDGA

/-! The concentrated-dg comparison is computed by the ordinary complex of
homogeneous components, including when its definition transports the dg algebra by equality. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedAlgebra DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard

namespace Beilinson.ConcentratedComparisonComponents

universe u
variable {R : Type u} [CommRing R]

/-- Keep the component computation together with the comparison while transporting models. -/
structure Data (B : DifferentialGradedAlgebra.{u,u} R) where
  comparison : ConcentratedDGA.Comparison B
  factor : ∀ (hzero : ∀ a : B.A, a ∈ B.grading 0) (hd : ∀ a : B.A, B.d a = 0),
    (toHomotopyCategory B ⋙ (quasiIsomorphisms B).Q) ⋙ comparison.equivalence.functor ≅
      ConcentratedComponents.functor B hzero hd ⋙ DerivedCategory.Q

def standard (R : Type u) [CommRing R] (S : Type u) [Ring S] [Algebra R S] :
    Data (degreeZero R S) where
  comparison := ConcentratedDGA.standardComparison R S
  factor _hzero _hd := degreeZeroDerivedComponentIso ≪≫
    Functor.isoWhiskerRight (ConcentratedComponents.standardIso R S).symm DerivedCategory.Q

theorem transport_comparison {B C : DifferentialGradedAlgebra.{u,u} R}
    (e : B = C) (d : Data B) :
    (e ▸ d).comparison = e ▸ d.comparison := by
  subst C
  rfl

variable (B : DifferentialGradedAlgebra.{u,u} R)
variable (hzero : ∀ a : B.A, a ∈ B.grading 0)
variable (hbot : ∀ q : ℤ, q ≠ 0 → B.grading q = ⊥)
variable (hd : ∀ a : B.A, B.d a = 0)

def data : Data B :=
  (ConcentratedDGA.eq_degreeZero_self B hzero hbot hd).symm ▸ standard R B.A

theorem data_comparison : (data B hzero hbot hd).comparison =
    ConcentratedDGA.comparison B hzero hbot hd :=
  transport_comparison _ _

/-- The actual chosen comparison, not merely an unspecified equivalent functor,
agrees with the complex of homogeneous components after localization. -/
def componentIso :
    (toHomotopyCategory B ⋙ (quasiIsomorphisms B).Q) ⋙
        (ConcentratedDGA.comparison B hzero hbot hd).equivalence.functor ≅
      ConcentratedComponents.functor B hzero hd ⋙ DerivedCategory.Q := by
  simpa only [data_comparison] using (data B hzero hbot hd).factor hzero hd

#print axioms componentIso

end Beilinson.ConcentratedComparisonComponents

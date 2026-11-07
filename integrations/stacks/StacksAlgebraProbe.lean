module

public import StacksFrontier.Homology.Perfect.BeilinsonAlgebra

/-! Compactness on the polynomial-matrix Beilinson algebra.
The geometric endomorphism ring has not been identified with this model here. -/

@[expose] public noncomputable section

open CategoryTheory StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

namespace Beilinson.StacksAlgebraProbe

universe u v

/-- On the polynomial-matrix algebra, perfectness is measured by finite total cohomology. -/
theorem compact_iff_finite_total_cohomology (k : Type u) [Field k] (n : ℕ)
    (K : DerivedCategory (ModuleCat.{v} (beilinsonAlgebra k n)ᵐᵒᵖ)) :
    IsCompactObject.{v} K ↔ HasFiniteTotalCohomology (k := k) K :=
  (hasFiniteTotalCohomology_iff_isCompactObject k n K).symm

#print axioms Beilinson.StacksAlgebraProbe.compact_iff_finite_total_cohomology

end Beilinson.StacksAlgebraProbe

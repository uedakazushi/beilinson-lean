module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEquivalenceLinear
public import DGAComparison

/-! Audit target for the upstream unbounded dg Beilinson equivalence.
The bounded coherent restriction and comparison with ordinary right modules are
not conclusions of this file. The upstream revision is fixed by the manifest. -/

@[expose] public noncomputable section

attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

namespace Beilinson.StacksBeilinsonProbe

universe u

open CategoryTheory Stacks.AlgebraicGeometry.Beilinson

/-- The audited upstream functor from dg modules to quasi-coherent complexes is an equivalence. -/
theorem unbounded_isEquivalence (A : Type u) [CommRing A] (n : ℕ) :
    (tensorWithGenerator A n).IsEquivalence :=
  tensorWithGenerator_isEquivalence A n

/-- The same functor preserves distinguished triangles and shifts. -/
theorem unbounded_isTriangulated (A : Type u) [CommRing A] (n : ℕ) :
    (tensorWithGenerator A n).IsTriangulated :=
  tensorWithGenerator_isTriangulated A n

/-- The dg algebra in the equivalence has the ordinary endomorphism ring as its underlying ring. -/
def ordinaryEndRingEquiv (A : Type u) [CommRing A] (n : ℕ) :
    (endAlgebra A n).A ≃+*
      CategoryTheory.End (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumModule A n) :=
  endAlgebraRingEquiv A n

/-- At universe zero, the geometric dg algebra is strictly the degree-zero ordinary End algebra.
The upstream degree-zero comparison uses a common universe for its base and algebra. -/
def geometricDegreeZeroIso (A : Type) [CommRing A] (n : ℕ) :
    endAlgebra A n ≅ DifferentialGradedAlgebra.degreeZero ℤ
      (CategoryTheory.End (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumModule A n)) :=
  Beilinson.DGAComparison.degreeZeroIso (endAlgebra A n)
    (AlgEquiv.ofRingEquiv (R := ℤ) (f := endAlgebraRingEquiv A n) (by intro z; simp))
    (endAlgebra_mem_grading_zero A n)
    (fun m hm => endAlgebra_grading_eq_bot A n hm)
    (fun x => by rw [endAlgebra_d_eq_zero]; rfl)

#print axioms Beilinson.StacksBeilinsonProbe.geometricDegreeZeroIso
#print axioms Beilinson.StacksBeilinsonProbe.ordinaryEndRingEquiv
#print axioms Beilinson.StacksBeilinsonProbe.unbounded_isEquivalence
#print axioms Beilinson.StacksBeilinsonProbe.unbounded_isTriangulated
#print axioms Stacks.AlgebraicGeometry.Beilinson.beilinson_equivalence

end Beilinson.StacksBeilinsonProbe

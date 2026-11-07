module

public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.Exactness

/-!
# Coordinate Koszul exactness on projective space

This optional probe checks a concrete geometric declaration. Its projective-space
model is Proj of the total-degree grading of A[X₀,…,Xₙ], not the separate
base-change model of projective space used by some higher-direct-image modules.
-/

@[expose] public section

namespace Beilinson.StacksGeometryProbe

universe u

/-- The coordinate Koszul complex on Proj(A[X₀,…,Xₙ]) is exact in all degrees. -/
theorem coordinate_koszul_acyclic (A : Type u) [CommRing A] (n : ℕ) (a : ℤ) :
    (Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulComplex A n a).Acyclic :=
  Stacks.AlgebraicGeometry.ProjKoszulComplex.acyclic_koszulComplex A n a

#print axioms Beilinson.StacksGeometryProbe.coordinate_koszul_acyclic

end Beilinson.StacksGeometryProbe

module

public import GeometricPerfectProbe
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic

/-! Instantiate the geometric compactness criterion on polynomial projective space.
The result concerns bounded coherent cohomology inside D_QCoh. -/

set_option autoImplicit false

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

namespace Beilinson.ProjectivePerfectProbe

universe u

/-- Projective space over any field is regular, including dimension zero. -/
theorem regular (k : Type u) [Field k] (n : ℕ) :
    IsRegular (AlgebraicGeometry.Proj (polyGrading k n)) := by
  let X := AlgebraicGeometry.Proj (polyGrading k n)
  exact ((isRegular_tfae X).out 1 2 rfl rfl).mpr
    ⟨inferInstance, Stacks.AlgebraicGeometry.ProjPolyChart.isRegularLocalRing_stalk_proj k n⟩

/-- The target finiteness condition for the bounded Beilinson restriction. -/
theorem compact_iff_boundedCoherent (k : Type u) [Field k] (n : ℕ)
    (K : Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading k n))) :
    IsCompactObject.{u} K ↔
      DerivedCategoryB.derivedCategoryBBounded
        (fun M : (AlgebraicGeometry.Proj (polyGrading k n)).Modules => M.IsCoherent) K.obj :=
  GeometricPerfectProbe.compact_iff_boundedCoherent _ (regular k n) K

#print axioms Beilinson.ProjectivePerfectProbe.regular
#print axioms Beilinson.ProjectivePerfectProbe.compact_iff_boundedCoherent

end Beilinson.ProjectivePerfectProbe

module

public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsCompactIsPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularBoundedCoherentPerfect

/-! The geometric bounded-coherent restriction, at the locally small derived model.
This does not identify the source endomorphism ring or construct the Beilinson functor. -/

set_option autoImplicit false

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

namespace Beilinson.GeometricPerfectProbe

universe u

/-- On a qcqs regular scheme, compact quasi-coherent objects have exactly bounded
coherent cohomology. This is an objectwise statement in D_QCoh, not yet D^b(Coh). -/
theorem compact_iff_boundedCoherent (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : IsRegular X)
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) :
    IsCompactObject.{u} K ↔
      DerivedCategoryB.derivedCategoryBBounded (fun M : X.Modules => M.IsCoherent) K.obj := by
  rw [Stacks.Duality.QcqsPerfect.isCompactObject_iff_isPerfect X K]
  change RingedSpace.IsPerfect (X := X.toRingedSpace) K.obj ↔ _
  exact Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_iff_isBoundedCoherent_of_isRegular
    hX K.obj

#print axioms Beilinson.GeometricPerfectProbe.compact_iff_boundedCoherent

end Beilinson.GeometricPerfectProbe

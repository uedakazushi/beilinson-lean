module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.ConeSignTransfer
public import StacksFrontier.Algebra.DGA.DerivedCategory

/-! Compare ordinary right modules with the cone convention used by the geometric
Beilinson functor. The primed and unprimed dg localizations have the same
underlying category at equal universes, but their triangles differ by a sign.
The homotopy comparison must therefore be precomposed with the sign-twisted
identity before descending it to the unprimed localization. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  DifferentialGradedAlgebra DifferentialGradedModule

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

namespace Beilinson.DegreeZeroConeComparison

universe u v

variable (R : Type u) [CommRing R] (S : Type u) [Ring S] [Algebra R S]

/-- The homogeneous-components functor with the shift sign of the cone convention. -/
def signedHomotopyFunctor :
    DifferentialGradedModule.HomotopyCategory (degreeZero R S) ⥤
      _root_.HomotopyCategory (ModuleCat.{u} Sᵐᵒᵖ) (.up ℤ) :=
  DifferentialGradedModule.signTwist (degreeZero R S) ⋙ degreeZeroHomotopyFunctor R Sᵐᵒᵖ

instance signedHomotopyFunctor_commShift : (signedHomotopyFunctor R S).CommShift ℤ :=
  inferInstanceAs ((DifferentialGradedModule.signTwist (degreeZero R S) ⋙
    degreeZeroHomotopyFunctor R Sᵐᵒᵖ).CommShift ℤ)

instance signedHomotopyFunctor_isTriangulated : (signedHomotopyFunctor R S).IsTriangulated := by
  let B := degreeZero R S
  let G := degreeZeroHomotopyFunctor R Sᵐᵒᵖ
  have hG : ∀ T, DifferentialGradedModule.IsDistinguishedTriangle B T →
      G.mapTriangle.obj T ∈ distTriang (_root_.HomotopyCategory (ModuleCat.{u} Sᵐᵒᵖ) (.up ℤ)) := by
    let := DifferentialGradedModule.instPretriangulatedHomotopyCategory' B
    let : G.IsTriangulated := degreeZeroHomotopyFunctor_isTriangulated
    exact mapTriangle_mem_distTriang_of_isTriangulated B G
  exact isTriangulated_signTwist_comp B G hG

variable [HasDerivedCategory.{v} (ModuleCat.{u} Sᵐᵒᵖ)]

/-- The ordinary right-module comparison on the cone-model dg derived category. -/
def coneRightModuleComparison :
    derivedCategory.{u, u, u} (degreeZero R S) ≌ DerivedCategory (ModuleCat.{u} Sᵐᵒᵖ) :=
  degreeZeroDerivedEquivalence (R := R) (S := S) (A := Sᵐᵒᵖ)

/-- With the corrected shift sign, the comparison preserves distinguished triangles. -/
theorem coneRightModuleComparison_exact :
    ∃ h : (coneRightModuleComparison R S).functor.CommShift ℤ, letI := h;
      (coneRightModuleComparison R S).functor.IsTriangulated := by
  let B := degreeZero R S
  let W := quasiIsomorphisms.{u, u, u} B
  let Q := W.Q
  let F := signedHomotopyFunctor R S ⋙ DerivedCategory.Qh
  let E := (coneRightModuleComparison R S).functor
  let : Localization.Lifting Q W F E := ⟨by
    change (quasiIsomorphisms' B).Q ⋙
        (degreeZeroDerivedEquivalence (R := R) (S := S) (A := Sᵐᵒᵖ)).functor ≅
      degreeZeroHomotopyFunctor R Sᵐᵒᵖ ⋙ DerivedCategory.Qh
    exact degreeZeroDerivedHomotopyIso⟩
  have := Localization.essSurj_mapArrow Q W
  let h := Functor.commShiftOfLocalization Q W ℤ F E
  refine ⟨h, ?_⟩
  let := h
  exact Functor.isTriangulated_of_precomp_iso (Localization.Lifting.iso Q W F E)

#print axioms Beilinson.DegreeZeroConeComparison.coneRightModuleComparison
#print axioms Beilinson.DegreeZeroConeComparison.coneRightModuleComparison_exact

end Beilinson.DegreeZeroConeComparison

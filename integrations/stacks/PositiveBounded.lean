module

public import MatrixBeilinson
public import PositiveWindow
public import CoherentTensorBounded
public import StacksFrontier.AlgebraicGeometry.ProjTwistCoherence.Basic

/-! The actual bounded derived twist and the negative-window Beilinson equivalence
followed by twisting by O(n). The generator comparison is in actual D^b(Coh),
not just in the ambient category of modules. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ExampleGenerator (twistModule twistFamily twistSumModule)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.gradedAlgebra

namespace Beilinson.PositiveBounded

variable (k : Type) [Field k] (n : ℕ)

local instance twistInvertible (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (polyGrading k n)).presheaf
      (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf.2 (twistModule k n d) :=
  Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf
    (polyGrading k n) (Stacks.AlgebraicGeometry.ProjTwistRank.degreeOneCover_polyGrading k n) d

/-- The actual twist autoequivalence on D^b(Coh P^n). -/
def twistEquivalence (d : ℤ) :=
  CoherentTensorBounded.equivalence (AlgebraicGeometry.Proj (polyGrading k n)) (twistModule k n d)

instance twistEquivalence_commShift (d : ℤ) : (twistEquivalence k n d).functor.CommShift ℤ :=
  inferInstanceAs ((CoherentTensorBounded.equivalence
    (AlgebraicGeometry.Proj (polyGrading k n)) (twistModule k n d)).functor.CommShift ℤ)

instance twistEquivalence_isTriangulated (d : ℤ) : (twistEquivalence k n d).functor.IsTriangulated :=
  inferInstanceAs ((CoherentTensorBounded.equivalence
    (AlgebraicGeometry.Proj (polyGrading k n)) (twistModule k n d)).functor.IsTriangulated)

/-- The negative-window generator as an actual coherent module. -/
def negativeModule : AlgebraicGeometry.SheafOfModules.CoherentModules
    (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf :=
  ⟨twistSumModule k n, CoherentTensorBounded.coherent_biproduct _ (twistFamily k n) (fun i =>
    AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_twistingSheaf_polyGrading k n (-(i : ℤ)))⟩

/-- The positive-window generator as an actual coherent module. -/
def positiveModule : AlgebraicGeometry.SheafOfModules.CoherentModules
    (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf :=
  ⟨PositiveWindow.positiveGenerator k n,
    CoherentTensorBounded.coherent_biproduct _ (PositiveWindow.positiveFamily k n) (fun i =>
      AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_twistingSheaf_polyGrading k n (i : ℤ))⟩

/-- E(n) ≅ T inside the actual category of coherent modules. -/
def coherentGeneratorIso :
    (CoherentTensor.equivalence (AlgebraicGeometry.Proj (polyGrading k n))
      (twistModule k n (n : ℤ))).functor.obj (negativeModule k n) ≅ positiveModule k n :=
  ObjectProperty.isoMk _ (PositiveWindow.generatorIso k n)

/-- The same generator comparison inside actual D^b(Coh P^n). -/
def derivedGeneratorIso :
    (twistEquivalence k n (n : ℤ)).functor.obj
        (CoherentTensorBounded.single _ (negativeModule k n)) ≅
      CoherentTensorBounded.single _ (positiveModule k n) :=
  CoherentTensorBounded.singleIso _ (twistModule k n (n : ℤ)) (negativeModule k n) ≪≫
    CoherentTensorBounded.singleMapIso _ (coherentGeneratorIso k n)

/-- The bounded Beilinson equivalence followed by the actual derived twist by O(n). -/
def equivalence := (MatrixBeilinson.equivalence k n).trans (twistEquivalence k n (n : ℤ))

instance equivalence_commShift : (equivalence k n).functor.CommShift ℤ := by
  change ((MatrixBeilinson.equivalence k n).functor ⋙
    (twistEquivalence k n (n : ℤ)).functor).CommShift ℤ
  infer_instance

instance equivalence_isTriangulated : (equivalence k n).functor.IsTriangulated := by
  change ((MatrixBeilinson.equivalence k n).functor ⋙
    (twistEquivalence k n (n : ℤ)).functor).IsTriangulated
  infer_instance

instance equivalence_inverseCommShift : (equivalence k n).inverse.CommShift ℤ :=
  (equivalence k n).commShiftInverse ℤ

instance equivalence_inverseIsTriangulated : (equivalence k n).inverse.IsTriangulated := by
  let E := equivalence k n
  let : E.toAdjunction.CommShift ℤ := E.toAdjunction.commShift_of_leftAdjoint ℤ
  exact E.toAdjunction.isTriangulated_rightAdjoint

#print axioms coherentGeneratorIso
#print axioms derivedGeneratorIso
#print axioms equivalence
#print axioms equivalence_inverseIsTriangulated

end Beilinson.PositiveBounded

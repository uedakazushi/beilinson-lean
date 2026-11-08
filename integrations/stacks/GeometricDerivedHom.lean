module

public import GeometricHomComplex
public import ConcentratedComparisonComponents
public import OrdinaryBeilinson
public import DerivedHomTransport

/-! Compare the actual geometric dg derived Hom, followed by the chosen ordinary
module comparison, with the independently right-derived ordinary Hom functor. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DifferentialGradedModule
open Stacks.AlgebraicGeometry.Beilinson

attribute [local instance 10000] HasDerivedCategory.standard

namespace Beilinson.GeometricDerivedHom

variable (A : Type) [CommRing A] (n : ℕ)

abbrev C := RingedSite.TensorModO.{0,0,0,0,0} (site A n)

local instance : IsGrothendieckAbelian.{0} (C A n) :=
  Stacks.SheafOfModules.sheafModulesGrothendieck _ _

/-- The comparison on complexes after both target localizations. -/
def complexesIso :
    RingedSite.homWithComplex (site A n) (generator A n) ⋙
      ((toHomotopyCategory (endAlgebra A n) ⋙ (quasiIsomorphisms (endAlgebra A n)).Q) ⋙
        (OrdinaryBeilinson.ordinaryComparison A n).equivalence.functor) ≅
    (GeometricHomComplex.ordinaryHom A n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q :=
  Functor.isoWhiskerLeft _
      (ConcentratedComparisonComponents.componentIso (endAlgebra A n)
        (endAlgebra_mem_grading_zero A n) (fun _ hq => endAlgebra_grading_eq_bot A n hq)
        (GeometricHomComplex.algebraDifferentialZero A n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (GeometricHomComplex.complexFunctorIso A n) DerivedCategory.Q

/-- The same comparison descends through homotopy classes. -/
def homotopyIso :
    RingedSite.homWithComplexToDerivedCategory (site A n) (generator A n) ⋙
      (OrdinaryBeilinson.ordinaryComparison A n).equivalence.functor ≅
    (GeometricHomComplex.ordinaryHom A n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh := by
  apply CategoryTheory.Quotient.natIsoLift
  refine (Iso.refl _) ≪≫ complexesIso A n ≪≫ ?_
  exact Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((GeometricHomComplex.ordinaryHom A n).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).symm _ ≪≫ Functor.associator _ _ _

/-- The actual dg-derived Hom, read through the chosen ordinary comparison. -/
def dgHom : DerivedCategory (C A n) ⥤
    DerivedCategory (ModuleCat (endAlgebra A n).Aᵐᵒᵖ) :=
  RingedSite.derivedHomWithComplex (site A n) (generator A n) ⋙
    (OrdinaryBeilinson.ordinaryComparison A n).equivalence.functor

def dgHomUnit :
    RingedSite.homWithComplexToDerivedCategory (site A n) (generator A n) ⋙
      (OrdinaryBeilinson.ordinaryComparison A n).equivalence.functor ⟶
    DerivedCategory.Qh ⋙ dgHom A n :=
  Functor.whiskerRight (RingedSite.derivedHomWithComplexUnit (site A n) (generator A n)) _ ≫
    (Functor.associator _ _ _).hom

instance dgHom_isRightDerived : (dgHom A n).IsRightDerivedFunctor (dgHomUnit A n)
    (HomotopyCategory.quasiIso (C A n) (ComplexShape.up ℤ)) := by
  dsimp only [dgHom, dgHomUnit]
  infer_instance

local instance ordinaryHasRightDerived :
    ((GeometricHomComplex.ordinaryHom A n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (C A n) (ComplexShape.up ℤ)) :=
  DerivedHomTransport.hasRightDerived (GeometricHomComplex.ordinaryHom A n)

/-- Independently derive the ordinary right-module Hom, after geometric coefficient change. -/
def classicalHom : DerivedCategory (C A n) ⥤
    DerivedCategory (ModuleCat (endAlgebra A n).Aᵐᵒᵖ) :=
  ((GeometricHomComplex.ordinaryHom A n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (C A n) (ComplexShape.up ℤ))

def classicalUnit :
    (GeometricHomComplex.ordinaryHom A n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ classicalHom A n :=
  ((GeometricHomComplex.ordinaryHom A n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (C A n) (ComplexShape.up ℤ))

instance classicalHom_isRightDerived :
    (classicalHom A n).IsRightDerivedFunctor (classicalUnit A n)
      (HomotopyCategory.quasiIso (C A n) (ComplexShape.up ℤ)) := by
  dsimp only [classicalHom, classicalUnit]
  infer_instance

/-- The dg and independently constructed classical ordinary right-module RHom
are naturally isomorphic as functors on the entire ambient derived category. -/
def derivedIso : dgHom A n ≅ classicalHom A n :=
  Functor.rightDerivedNatIso _ _ (dgHomUnit A n) (classicalUnit A n)
    (HomotopyCategory.quasiIso (C A n) (ComplexShape.up ℤ)) (homotopyIso A n)

/-- Change from ordinary End(E) coefficients to the underlying geometric dg ring. -/
def changeRing : ModuleCat (End (generatorModule A n))ᵐᵒᵖ ⥤
    ModuleCat (endAlgebra A n).Aᵐᵒᵖ :=
  ModuleCat.restrictScalars (RingEquiv.op (endAlgebraRingEquivTensorModO A n)).toRingHom

instance changeRing_isEquivalence : (changeRing A n).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv _

instance changeRing_additive : (changeRing A n).Additive := by
  dsimp only [changeRing]
  infer_instance

/-- Deriving ordinary Hom before or after this exact coefficient change agrees. -/
def changeRingDerivedIso :
    DerivedHomTransport.derivedHom (generatorModule A n) ⋙ (changeRing A n).mapDerivedCategory ≅
      classicalHom A n := by
  letI := DerivedHomTransport.hasRightDerived (preadditiveCoyonedaObj (generatorModule A n))
  exact Functor.totalRightDerivedMapHomotopyCompIsoOfEquivalence (𝟭 (C A n))
      (preadditiveCoyonedaObj (generatorModule A n)) (GeometricHomComplex.ordinaryHom A n)
      (changeRing A n) (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryIdIso (C A n)) _ ≪≫
    Functor.leftUnitor _

/-- The actual dg RHom, read through the chosen comparison, is the classical
ordinary RHom(E,-), with the explicit geometric coefficient-ring identification. -/
def ordinaryDerivedIso : dgHom A n ≅
    DerivedHomTransport.derivedHom (generatorModule A n) ⋙ (changeRing A n).mapDerivedCategory :=
  derivedIso A n ≪≫ (changeRingDerivedIso A n).symm

#print axioms ordinaryDerivedIso
#print axioms derivedIso
#print axioms complexesIso
#print axioms homotopyIso

end Beilinson.GeometricDerivedHom

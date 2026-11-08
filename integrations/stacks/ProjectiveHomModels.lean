module

public import Beilinson.EndRingYoneda
public import DerivedEquivalenceModels
public import GeometricEndHom
public import PositiveDerivedHom

/-! Compare the classical Hom definitions in the standard sheaf-module model
and in the locally small geometric model used by the Beilinson equivalence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.Beilinson
open Stacks.AlgebraicGeometry.ExampleGenerator (twistSumModule)
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] SheafOfModules.hasDerivedCategory Scheme.Modules.hasDerivedCategory

namespace Beilinson.ProjectiveHomModels

variable (A : Type) [CommRing A] (n : ℕ)

local instance moduleDerivedCategory (R : Type) [Ring R] :
    HasDerivedCategory (ModuleCat.{0} R) := HasDerivedCategory.standard _

local instance schemeGrothendieck : IsGrothendieckAbelian.{0}
    (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  Stacks.SheafOfModules.sheafModulesGrothendieck _ _

local instance siteGrothendieck : IsGrothendieckAbelian.{0} (GeometricDerivedHom.C A n) :=
  Stacks.SheafOfModules.sheafModulesGrothendieck _ _

/-- The two sheaf-module spellings give the same ordinary Hom with the specified End ring map. -/
def underivedIso :
    preadditiveCoyonedaObj (generatorModule A n) ⋙
      ModuleCat.restrictScalars.{0} (RingEquiv.op (endModulesRingEquiv A n).symm).toRingHom ≅
    (modulesEquivalence A n).functor ⋙ preadditiveCoyonedaObj (twistSumModule A n) :=
  EndRingYoneda.functorIso (modulesEquivalence A n).functor (generatorModule A n)
    (Y := twistSumModule A n) (Iso.refl _) (endModulesRingEquiv A n) (by
      intro a
      change a.asHom = 𝟙 _ ≫ a.asHom ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id])

#print axioms underivedIso

/-- The model comparison commutes with independently defined classical RHom(E,-). -/
def standardToSmallIso : GeometricEndHom.classicalEndHom A n ≅
    (modelEquivalence A n).functor ⋙ PositiveDerivedHom.negativeHom A n := by
  let H := ModuleCat.restrictScalars.{0} (RingEquiv.op (endModulesRingEquiv A n).symm).toRingHom
  letI : H.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv _
  exact DerivedEquivalenceModels.transport
    (HasDerivedCategory.standard (GeometricDerivedHom.C A n))
    (Scheme.Modules.hasDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)))
    (modulesEquivalence A n).functor (preadditiveCoyonedaObj (generatorModule A n))
    (preadditiveCoyonedaObj (twistSumModule A n)) H (underivedIso A n)

#print axioms standardToSmallIso

end Beilinson.ProjectiveHomModels

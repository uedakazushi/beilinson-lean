module

public import Beilinson.KroneckerEnd
public import Beilinson.KroneckerEndModules
public import SheafHomSections
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Derived
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.DerivedTwistSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistMonomialBasis

/-! The actual geometric Kronecker endomorphism algebra on the projective line.
The twists here are sheaves on polynomial Proj, with base-linear Hom spaces. -/

set_option autoImplicit false

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open Stacks.ProjectiveSpace.Cohomology

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] hasSheafify_opens_topCat wEqualsLocallyBijective_opens_topCat
  hasSheafify_opens_scheme wEqualsLocallyBijective_opens_scheme

namespace Beilinson.ProjectiveLineEnd

universe u

abbrev line (k : Type u) [CommRing k] (d : ℤ) : (AlgebraicGeometry.Proj (polyGrading k 1)).Modules :=
  ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k 1) d
abbrev unitModule (k : Type u) [CommRing k] : (AlgebraicGeometry.Proj (polyGrading k 1)).Modules :=
  SheafHomSections.unitObject (AlgebraicGeometry.Proj (polyGrading k 1))

variable (k : Type u) [Field k]

local instance lineLinear : Linear k (AlgebraicGeometry.Proj (polyGrading k 1)).Modules := Scheme.linearOver (projToSpecCoeff k 1)
local instance sectionsLinear : (globalSectionsOver (projToSpecCoeff k 1)).Linear k :=
  globalSectionsOver_linearOver (projToSpecCoeff k 1)

local instance finiteBiproducts : HasFiniteBiproducts (AlgebraicGeometry.Proj (polyGrading k 1)).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

def zeroIso : line k 0 ≅ unitModule k := twistingSheafZeroIso k 1

/-- Global sections as homogeneous polynomials, with the base scalar action retained. -/
def sectionsHomogeneousIso (d : ℤ) (hd : 0 ≤ d) :
    (globalSectionsOver (projToSpecCoeff k 1)).obj (line k d) ≅
      ModuleCat.of k (MvPolynomial.homogeneousSubmodule (Fin 2) k d.toNat) :=
  globalSectionsOverTwistingSheafIso k 1 d ≪≫ twistCohomologyIsoHomogeneous k 1 d hd

def rawUnitHomEquiv (d : ℤ) : (unitModule k ⟶ line k d) ≃ₗ[k]
    (globalSectionsOver (projToSpecCoeff k 1)).obj (line k d) :=
  SheafHomSections.unitHomLinearEquivOfLinear (projToSpecCoeff k 1) (line k d)

/-- Dimension of Hom(O,O(d)), computed through the two separately checked comparisons. -/
theorem unitToTwist_finrank (d : ℤ) (hd : 0 ≤ d) :
    Module.finrank k (unitModule k ⟶ line k d) = d.toNat + 1 := by
  have hH := (rawUnitHomEquiv k d).finrank_eq
  have hS := (sectionsHomogeneousIso k d hd).toLinearEquiv.finrank_eq
  have hP := Module.finrank_eq_card_basis (MvPolynomial.homogeneousBinaryBasis k d.toNat)
  exact hH.trans (hS.trans (by simpa using hP))

theorem unit_finrank : Module.finrank k (unitModule k ⟶ unitModule k) = 1 := by
  have h := (Linear.homCongr k (Iso.refl (unitModule k))
    (zeroIso k)).finrank_eq
  exact h.symm.trans (unitToTwist_finrank k 0 (by omega))

/-- Twisting is base-linear, via tensor symmetry and the checked scalar comparison. -/
theorem twist_linear (d : ℤ) : (twistModules k 1 d).Linear k := by
  let F : (AlgebraicGeometry.Proj (polyGrading k 1)).Modules ⥤
      (AlgebraicGeometry.Proj (polyGrading k 1)).Modules :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u}
      (AlgebraicGeometry.Proj (polyGrading k 1)).sheaf).flip.obj (line k d)
  have hF : F.Linear k := SheafHomSections.tensorRightLinear (projToSpecCoeff k 1) (line k d)
  rw [Functor.linear_iff]
  intro M a
  exact (Functor.linear_iff k F).mp hF M a

def twistOneToUnitIso : (twistModules k 1 (-1)).obj (line k 1) ≅ unitModule k :=
  twistModulesTwistingSheafIso k 1 1 (-1) ≪≫ zeroIso k

def twistUnitIso : (twistModules k 1 (-1)).obj (unitModule k) ≅ line k (-1) :=
  (twistModules k 1 (-1)).mapIso (zeroIso k).symm ≪≫
    twistModulesTwistingSheafIso k 1 0 (-1)

theorem one_finrank : Module.finrank k (line k 1 ⟶ line k 1) = 1 := by
  let F := twistModules k 1 (-1)
  let : F.Linear k := twist_linear k (-1)
  have hF := KroneckerEnd.finrank_hom_map k (X := line k 1) (Y := line k 1) F
  have hI := KroneckerEnd.finrank_hom_congr k (twistOneToUnitIso k) (twistOneToUnitIso k)
  exact hF.trans (hI.trans (unit_finrank k))

local instance reverseUnitHom : Subsingleton (line k 1 ⟶ unitModule k) := by
  have hz := isZero_twistCohomology k 1 (-1) 0 (by omega)
  let : Subsingleton ((globalSectionsOver (projToSpecCoeff k 1)).obj (line k (-1))) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (hz.of_iso (globalSectionsOverTwistingSheafIso k 1 (-1)))
  let : Subsingleton (unitModule k ⟶ line k (-1)) :=
    (rawUnitHomEquiv k (-1)).toEquiv.subsingleton
  let F := twistModules k 1 (-1)
  let : Subsingleton (F.obj (line k 1) ⟶ F.obj (unitModule k)) :=
    KroneckerEnd.subsingleton_hom_congr k (twistOneToUnitIso k) (twistUnitIso k)
  exact ⟨fun f g => F.map_injective (Subsingleton.elim _ _)⟩

theorem forward_finrank : Module.finrank k (line k 0 ⟶ line k 1) = 2 := by
  have h := (Linear.homCongr k (zeroIso k) (Iso.refl (line k 1))).finrank_eq
  exact h.trans (unitToTwist_finrank k 1 (by omega))

theorem zero_finrank : Module.finrank k (line k 0 ⟶ line k 0) = 1 :=
  (Linear.homCongr k (zeroIso k) (zeroIso k)).finrank_eq.trans
    (unit_finrank k)

local instance reverseHom : Subsingleton (line k 1 ⟶ line k 0) :=
  KroneckerEnd.subsingleton_hom_congr k (Iso.refl (line k 1)) (zeroIso k)

/-- The geometric, positive-window endomorphism algebra on P^1 is Kronecker. -/
def algebraEquiv : Kronecker.Algebra k ≃ₐ[k] End (line k 0 ⊞ line k 1) :=
  Classical.choice (KroneckerEnd.nonemptyAlgebraEquivOfFinrank k
    (zero_finrank k) (one_finrank k) (forward_finrank k))

theorem finrank : Module.finrank k (End (line k 0 ⊞ line k 1)) = 4 :=
  (algebraEquiv k).toLinearEquiv.finrank_eq.symm.trans (Kronecker.finrank k)

/-- All ordinary right modules over the actual geometric End ring have dimension at most one. -/
theorem projectiveDimension_le_one
    (M : ModuleCat.{u} (End (line k 0 ⊞ line k 1))ᵐᵒᵖ) :
    projectiveDimension M ≤ 1 :=
  KroneckerEndModules.projectiveDimension_le_one (algebraEquiv k).toRingEquiv M

#print axioms Beilinson.ProjectiveLineEnd.projectiveDimension_le_one
#print axioms Beilinson.ProjectiveLineEnd.twist_linear
#print axioms Beilinson.ProjectiveLineEnd.algebraEquiv
#print axioms Beilinson.ProjectiveLineEnd.finrank

end Beilinson.ProjectiveLineEnd

module

public import Beilinson.EndTransport
public import ProjectiveLineEnd
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.QuasiCoherentGenerator

/-! The negative-window generator used by the dg equivalence has the same
Kronecker algebra as the positive-window generator on the actual projective line. -/

set_option autoImplicit false

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open Stacks.AlgebraicGeometry.ExampleGenerator (twistFamily twistSumModule)
open Stacks.ProjectiveSpace.Cohomology
open Beilinson.ProjectiveLineEnd (line unitModule)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Beilinson.ProjectiveLineWindow

universe u
variable (k : Type u) [Field k]

local instance baseLinear : Linear k (AlgebraicGeometry.Proj (polyGrading k 1)).Modules :=
  ProjectiveLineEnd.lineLinear k
local instance finiteBiproducts : HasFiniteBiproducts
    (AlgebraicGeometry.Proj (polyGrading k 1)).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

def twistNegativeIso : (twistModules k 1 1).obj (line k (-1)) ≅ line k 0 :=
  twistModulesTwistingSheafIso k 1 (-1) 1

def twistZeroIso : (twistModules k 1 1).obj (line k 0) ≅ line k 1 :=
  twistModulesTwistingSheafIso k 1 0 1

theorem negative_finrank : Module.finrank k (line k (-1) ⟶ line k (-1)) = 1 := by
  let F := twistModules k 1 1
  let : F.Linear k := ProjectiveLineEnd.twist_linear k 1
  have hF := KroneckerEnd.finrank_hom_map k (X := line k (-1)) (Y := line k (-1)) F
  have hI := KroneckerEnd.finrank_hom_congr k (twistNegativeIso k) (twistNegativeIso k)
  exact hF.trans (hI.trans (ProjectiveLineEnd.zero_finrank k))

theorem forward_finrank : Module.finrank k (line k (-1) ⟶ line k 0) = 2 := by
  let F := twistModules k 1 1
  let : F.Linear k := ProjectiveLineEnd.twist_linear k 1
  have hF := KroneckerEnd.finrank_hom_map k (X := line k (-1)) (Y := line k 0) F
  have hI := KroneckerEnd.finrank_hom_congr k (twistNegativeIso k) (twistZeroIso k)
  exact hF.trans (hI.trans (ProjectiveLineEnd.forward_finrank k))

local instance unitNegativeHom : Subsingleton (unitModule k ⟶ line k (-1)) := by
  have hz := isZero_twistCohomology k 1 (-1) 0 (by omega)
  let : Subsingleton ((globalSectionsOver (projToSpecCoeff k 1)).obj (line k (-1))) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (hz.of_iso (globalSectionsOverTwistingSheafIso k 1 (-1)))
  exact (ProjectiveLineEnd.rawUnitHomEquiv k (-1)).toEquiv.subsingleton

local instance reverseHom : Subsingleton (line k 0 ⟶ line k (-1)) :=
  KroneckerEnd.subsingleton_hom_congr k (ProjectiveLineEnd.zeroIso k) (Iso.refl _)

def orderedNegativeAlgebraEquiv : Kronecker.Algebra k ≃ₐ[k] End (line k (-1) ⊞ line k 0) :=
  Classical.choice (KroneckerEnd.nonemptyAlgebraEquivOfFinrank k
    (negative_finrank k) (ProjectiveLineEnd.zero_finrank k) (forward_finrank k))

/-- Match the actual Fin 2 direct sum in the unbounded theorem, including its order. -/
def generatorIso : twistSumModule k 1 ≅ line k (-1) ⊞ line k 0 :=
  EndTransport.pairIso (twistFamily k 1) ≪≫ biprod.braiding _ _

/-- The actual ordinary End(E) ring of the unbounded theorem, identified with Kronecker. -/
def algebraEquiv : Kronecker.Algebra k ≃ₐ[k] End (twistSumModule k 1) :=
  (orderedNegativeAlgebraEquiv k).trans (EndTransport.iso k (generatorIso k).symm)

/-- Scalar-free form for the ordinary module-category adapters. -/
def ringEquiv : Kronecker.Algebra k ≃+* End (twistSumModule k 1) :=
  (algebraEquiv k).toRingEquiv

/-- The positive and negative geometric windows have isomorphic endomorphism algebras. -/
def windowAlgebraEquiv : End (twistSumModule k 1) ≃ₐ[k] End (line k 0 ⊞ line k 1) :=
  (algebraEquiv k).symm.trans (ProjectiveLineEnd.algebraEquiv k)

#print axioms Beilinson.ProjectiveLineWindow.algebraEquiv
#print axioms Beilinson.ProjectiveLineWindow.windowAlgebraEquiv

end Beilinson.ProjectiveLineWindow

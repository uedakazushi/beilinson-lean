module

public import GeometricHomEvaluation
public import ConcentratedComponents

/-! The actual dg Hom module, read on homogeneous components, is the ordinary
complex of right End(E)-module Homs, with the geometric coefficient identification. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.Beilinson

namespace Beilinson.GeometricHomComplex

universe u
variable (A : Type u) [CommRing A] (n : ℕ)

theorem algebraDifferentialZero (a : (endAlgebra A n).A) : (endAlgebra A n).d a = 0 := by
  rw [endAlgebra_d_eq_zero]
  rfl

/-- The ordinary right-End Hom functor, written over the geometric dg ring. -/
def ordinaryHom : RingedSite.TensorModO.{u,u,u,u,u} (site A n) ⥤
    ModuleCat.{u} (endAlgebra A n).Aᵐᵒᵖ :=
  preadditiveCoyonedaObj (generatorModule A n) ⋙
    ModuleCat.restrictScalars (RingEquiv.op (endAlgebraRingEquivTensorModO A n)).toRingHom

instance ordinaryHom_additive : (ordinaryHom A n).Additive := by
  dsimp only [ordinaryHom]
  infer_instance

variable (I : CochainComplex (RingedSite.TensorModO.{u,u,u,u,u} (site A n)) ℤ)

/-- Evaluation is linear for the actual right endomorphism ring, not only for ℤ. -/
def moduleEquiv (q : ℤ) :
    ConcentratedComponents.component (endAlgebra A n) (endAlgebra_mem_grading_zero A n)
      ((GeometricHomEvaluation.representation A n).functor.obj I) q ≃ₗ[(endAlgebra A n).Aᵐᵒᵖ]
        (ordinaryHom A n).obj (I.X q) where
  toEquiv := (GeometricHomEvaluation.evaluation A n I q).toEquiv
  map_add' := (GeometricHomEvaluation.evaluation A n I q).map_add
  map_smul' a z := by
    let := ConcentratedComponents.componentModule (endAlgebra A n)
      (endAlgebra_mem_grading_zero A n) ((GeometricHomEvaluation.representation A n).functor.obj I) q
    change ((GeometricHomEvaluation.representation A n).functor.obj I).grading q at z
    obtain ⟨c, hc, he⟩ := GeometricHomEvaluation.action A n I q z a.unop
    have hc' : c = a • z := Subtype.ext hc
    rw [← hc']
    exact he

/-- The entire component complex agrees with termwise ordinary right-module Hom. -/
def complexIso :
    ConcentratedComponents.complex (endAlgebra A n) (endAlgebra_mem_grading_zero A n)
      (algebraDifferentialZero A n) ((GeometricHomEvaluation.representation A n).functor.obj I) ≅
      ((ordinaryHom A n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
  HomologicalComplex.Hom.isoOfComponents (fun q => (moduleEquiv A n I q).toModuleIso) (by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    dsimp only [ConcentratedComponents.complex]
    rw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (GeometricHomEvaluation.differential A n I i z).symm)

/-- Evaluate the actual geometric dg Hom functor as a functor of ordinary complexes. -/
def componentFunctor :
    CochainComplex (RingedSite.TensorModO.{u,u,u,u,u} (site A n)) ℤ ⥤
      CochainComplex (ModuleCat.{u} (endAlgebra A n).Aᵐᵒᵖ) ℤ :=
  RingedSite.homWithComplex.{u,u,u,u,u} (site A n) (generator A n) ⋙
    ConcentratedComponents.functor (endAlgebra A n) (endAlgebra_mem_grading_zero A n)
      (algebraDifferentialZero A n)

/-- The component comparison is natural in arbitrary complexes of sheaf modules. -/
def complexFunctorIso : componentFunctor A n ≅
    (ordinaryHom A n).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents (complexIso A n) (by
    intro I J f
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((GeometricHomEvaluation.representation A n).functor.obj I).grading q at z
    obtain ⟨c, hc, he⟩ := GeometricHomEvaluation.postcompose A n I f q z
    have hc' : c = ((RingedSite.homWithComplex.{u,u,u,u,u}
        (site A n) (generator A n)).map f).gradedMap q z := Subtype.ext hc
    change GeometricHomEvaluation.evaluation A n J q
      (((RingedSite.homWithComplex.{u,u,u,u,u}
        (site A n) (generator A n)).map f).gradedMap q z) =
      GeometricHomEvaluation.evaluation A n I q z ≫ f.f q
    rw [← hc']
    exact he)

#print axioms complexFunctorIso
#print axioms moduleEquiv
#print axioms complexIso

end Beilinson.GeometricHomComplex

module

public import OrdinaryBeilinson
public import CentralDegreeZero

/-! The ordinary negative-window Beilinson functor is linear over the geometric
coefficient ring, even though its dg algebra is declared over the integers. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.Beilinson
open scoped ModuleCat.Algebra

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [local instance] tensorModOLinear projectiveSpaceModulesLinear

namespace Beilinson.OrdinaryBeilinsonLinear

local instance moduleDerivedCategory (S : Type) [Ring S] :
    HasDerivedCategory (ModuleCat.{0} S) := HasDerivedCategory.standard _

variable (A : Type) [CommRing A] (n : ℕ)

/-- The geometric scalars give the ordinary endomorphism dg ring an A-algebra structure. -/
@[instance_reducible] def scalarAlgebra : Algebra A (endAlgebra A n).A :=
  (scalarRingHom A n).toAlgebra' (fun a => (isCentralCocycle_scalarRingHom A n a).comm)

local instance : Algebra A (endAlgebra A n).A := scalarAlgebra A n

/-- The source carries the usual coefficient action on ordinary module complexes. -/
@[instance_reducible] def ordinaryLinear :
    Linear A (OrdinaryBeilinson.ordinaryDerivedCategory A n) := inferInstance

local instance : Linear A (OrdinaryBeilinson.ordinaryDerivedCategory A n) := ordinaryLinear A n
local instance : Linear A (derivedCategoryR A n) := derivedCategoryRLinear A n
local instance : Linear A (Stacks.Duality.quasiCoherentDerivedCategory
    (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n))) :=
  quasiCoherentDerivedCategoryLinear A n

/-- The comparison from dg modules to ordinary right modules is A-linear. -/
theorem comparison_linear : (OrdinaryBeilinson.ordinaryComparison A n).equivalence.functor.Linear A := by
  with_unfolding_all
    exact CentralDegreeZero.concentrated_functor_linear A (endAlgebra A n)
      (endAlgebra_mem_grading_zero A n)
      (fun m hm => endAlgebra_grading_eq_bot A n hm)
      (fun x => by rw [endAlgebra_d_eq_zero]; rfl)

/-- The inverse comparison is A-linear as well. -/
theorem comparison_inverse_linear :
    (OrdinaryBeilinson.ordinaryComparison A n).equivalence.inverse.Linear A := by
  let : (OrdinaryBeilinson.ordinaryComparison A n).equivalence.functor.Linear A := comparison_linear A n
  infer_instance

/-- The actual ordinary-module tensor equivalence preserves geometric coefficients. -/
theorem ordinaryTensor_linear : (OrdinaryBeilinson.ordinaryTensor A n).Linear A := by
  let : (OrdinaryBeilinson.ordinaryComparison A n).equivalence.inverse.Linear A :=
    comparison_inverse_linear A n
  let : (tensorWithGenerator A n).Linear A := tensorWithGenerator_linear A n
  change ((OrdinaryBeilinson.ordinaryComparison A n).equivalence.inverse ⋙
    tensorWithGenerator A n).Linear A
  infer_instance

/-- The geometric dg-to-End ring comparison sends coefficients to the usual scalar endomorphisms. -/
theorem endAlgebraToEnd_scalar (a : A) :
    endAlgebraToEnd A n (scalarRingHom A n a) = a • 1 := by
  apply End.ext
  rw [endAlgebraToEnd]
  have h : (⟨scalarRingHom A n a, endAlgebra_mem_grading_zero A n _⟩ :
      (endAlgebra A n).grading 0) = scalarHom A n a := rfl
  rw [h, algebraHom_scalarHom, CochainComplex.HomComplex.Cochain.smul_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.id_f]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp,
    Iso.hom_inv_id, End.smul_asHom, End.one_asHom]

/-- The geometric ring comparison is an algebra equivalence for the actual base scalars. -/
def endAlgebraEquiv : (endAlgebra A n).A ≃ₐ[A]
    End (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumModule A n) :=
  { endAlgebraRingEquiv A n with
    commutes' := fun a => by
      change endAlgebraToEnd A n (scalarRingHom A n a) = a • 1
      exact endAlgebraToEnd_scalar A n a }

/-- Changing rings along the geometric End comparison preserves base coefficients. -/
theorem restrictEnd_linear : (OrdinaryBeilinson.restrictEnd A n).Linear A := by
  rw [Functor.linear_iff]
  intro M a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (algebraMap A (End (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumModule A n))ᵐᵒᵖ a) • x =
    (RingEquiv.op (endAlgebraRingEquiv A n))
      (algebraMap A (endAlgebra A n).Aᵐᵒᵖ a) • x
  exact congrArg (fun c => c • x) ((AlgEquiv.op (endAlgebraEquiv A n)).commutes a).symm

/-- The actual End(E)-module tensor equivalence preserves the geometric coefficient ring. -/
theorem endTensor_linear : (OrdinaryBeilinson.endTensor A n).Linear A := by
  let : (OrdinaryBeilinson.restrictEnd A n).Linear A := restrictEnd_linear A n
  let : (OrdinaryBeilinson.ordinaryTensor A n).Linear A := ordinaryTensor_linear A n
  change ((OrdinaryBeilinson.restrictEnd A n).mapDerivedCategory ⋙
    OrdinaryBeilinson.ordinaryTensor A n).Linear A
  infer_instance

#print axioms endTensor_linear
#print axioms restrictEnd_linear
#print axioms endAlgebraEquiv
#print axioms endAlgebraToEnd_scalar
#print axioms comparison_linear
#print axioms comparison_inverse_linear
#print axioms ordinaryTensor_linear

end Beilinson.OrdinaryBeilinsonLinear

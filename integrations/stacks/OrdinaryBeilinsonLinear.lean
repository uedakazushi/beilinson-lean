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

namespace Beilinson.OrdinaryBeilinsonLinear

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

#print axioms comparison_linear
#print axioms comparison_inverse_linear
#print axioms ordinaryTensor_linear

end Beilinson.OrdinaryBeilinsonLinear

module

public import ConcentratedDGA
public import StacksFrontier.Algebra.DGA.CentralAction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroDerivedStructure

/-! The degree-zero comparison respects a central coefficient ring in addition
to the dg algebra's declared base ring. This is needed for finiteness over the
geometric base field when the dg algebra is presented over the integers. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedAlgebra DifferentialGradedModule
open scoped ModuleCat.Algebra

namespace Beilinson.CentralDegreeZero

universe u w

section General
variable {R : Type u} [CommRing R] (E : DifferentialGradedAlgebra.{u,u} R)
variable (K : Type u) [CommRing K] (ψ : K →+* E.A)
  (hψ : ∀ a, IsCentralCocycle (ψ a))

/-- Localization is linear for the action of central closed degree-zero elements. -/
theorem localization_linear :
    letI := Linear.ofRingMorphism (centerRingHom.{u,u,u} ψ hψ)
    letI := derivedLinearOfCentral.{u,u,u} ψ hψ
    (toHomotopyCategory E ⋙ (quasiIsomorphisms.{u,u,u} E).Q).Linear K := by
  let := Linear.ofRingMorphism (centerRingHom.{u,u,u} ψ hψ)
  let := derivedLinearOfCentral.{u,u,u} ψ hψ
  rw [Functor.linear_iff]
  intro M a
  change (toHomotopyCategory E ⋙ (quasiIsomorphisms.{u,u,u} E).Q).map
      ((centerRingHom ψ hψ a).app M ≫ 𝟙 M) =
    (derivedCenterRingHom ψ hψ a).app
      ((toHomotopyCategory E ⋙ (quasiIsomorphisms.{u,u,u} E).Q).obj M) ≫ 𝟙 _
  simp only [Category.comp_id, Functor.comp_map, Functor.comp_obj,
    derivedCenterRingHom_app, homotopyCenterRingHom_app, centerRingHom_app]

end General

section DegreeZero
variable (R K S : Type u) [CommRing R] [CommRing K] [Ring S] [Algebra R S] [Algebra K S]

/-- Every coefficient scalar is central and closed in the degree-zero dg algebra. -/
theorem scalarCocycle (a : K) : IsCentralCocycle (E := degreeZero R S) (algebraMap K S a) :=
  ⟨fun b => Algebra.commutes a b, by simp [degreeZero, degreeZeroGrading], rfl⟩

/-- The extra coefficient ring acts through the center, rather than the declared dg base. -/
@[instance_reducible] def moduleLinear : Linear K (DifferentialGradedModule.{u,u,u} (degreeZero R S)) :=
  Linear.ofRingMorphism (centerRingHom (algebraMap K S) (scalarCocycle R K S))

local instance : Linear K (DifferentialGradedModule.{u,u,u} (degreeZero R S)) := moduleLinear R K S

/-- Taking homogeneous components preserves the additional central coefficient action. -/
theorem component_linear : (degreeZeroComponentFunctor R Sᵐᵒᵖ).Linear K := by
  rw [Functor.linear_iff]
  intro M a
  ext i x
  apply Subtype.ext
  rfl

local instance derivedLinear : Linear K (derivedCategory' (degreeZero R S)) :=
  derivedLinearOfCentral (algebraMap K S) (scalarCocycle R K S)

variable [HasDerivedCategory.{w} (ModuleCat.{u} Sᵐᵒᵖ)]

/-- The ordinary right-module comparison preserves an additional central coefficient ring. -/
theorem equivalence_functor_linear :
    (degreeZeroDerivedEquivalence (R := R) (S := S) (A := Sᵐᵒᵖ)).functor.Linear K := by
  let : (degreeZeroComponentFunctor R Sᵐᵒᵖ).Linear K := component_linear R K S
  let : (toHomotopyCategory (degreeZero R S) ⋙
      (quasiIsomorphisms' (degreeZero R S)).Q).Linear K :=
    localization_linear (degreeZero R S) K (algebraMap K S) (scalarCocycle R K S)
  have := degreeZero_localization (R := R) (A := Sᵐᵒᵖ)
  rw [← Localization.functor_linear_iff
    (toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q)
    ((HomologicalComplex.quasiIso (ModuleCat.{u} Sᵐᵒᵖ) (.up ℤ)).inverseImage
      (degreeZeroComponentFunctor R Sᵐᵒᵖ)) K
    (degreeZeroComponentFunctor R Sᵐᵒᵖ ⋙ DerivedCategory.Q)
    (degreeZeroDerivedEquivalence (R := R) (S := S) (A := Sᵐᵒᵖ)).functor]
  infer_instance

end DegreeZero

section Concentrated
variable {R : Type u} [CommRing R] (K : Type u) [CommRing K]
variable (B : DifferentialGradedAlgebra.{u,u} R) [Algebra K B.A]
variable (hzero : ∀ x : B.A, x ∈ B.grading 0)
  (hbot : ∀ n : ℤ, n ≠ 0 → B.grading n = ⊥) (hd : ∀ x : B.A, B.d x = 0)

include hzero hd in
theorem concentratedScalarCocycle (a : K) : IsCentralCocycle (E := B) (algebraMap K B.A a) :=
  ⟨fun b => Algebra.commutes a b, hzero _, hd _⟩

local instance : HasDerivedCategory (ModuleCat.{u} B.Aᵐᵒᵖ) := HasDerivedCategory.standard _

/-- The checked concentrated-dg comparison also respects a central coefficient algebra. -/
theorem concentrated_functor_linear :
    letI := derivedLinearOfCentral.{u,u,u} (algebraMap K B.A) (concentratedScalarCocycle K B hzero hd)
    (ConcentratedDGA.comparison B hzero hbot hd).equivalence.functor.Linear K := by
  let := derivedLinearOfCentral.{u,u,u} (algebraMap K B.A) (concentratedScalarCocycle K B hzero hd)
  have hg : B.grading = degreeZeroGrading R B.A := by
    funext n
    by_cases hn : n = 0
    · subst n
      rw [degreeZeroGrading_zero]
      exact Submodule.eq_top_iff'.2 hzero
    · rw [degreeZeroGrading_eq_bot R B.A hn]
      exact hbot n hn
  have hd0 : B.d = 0 := LinearMap.ext hd
  cases B with
  | @mk A ringA algA grading graded d hdd hmem hleib =>
    change grading = degreeZeroGrading R A at hg
    change d = (0 : A →ₗ[R] A) at hd0
    subst grading
    subst d
    have hp : graded = (degreeZero R A).gradedAlg :=
      ConcentratedDGA.gradedAlgebra_unique _ _ _
    subst graded
    let : HasDerivedCategory (ModuleCat.{u} Aᵐᵒᵖ) := HasDerivedCategory.standard _
    with_unfolding_all
      exact equivalence_functor_linear R K A

/-- The inverse, from ordinary right modules to dg modules, is coefficient-linear too. -/
theorem concentrated_inverse_linear :
    letI := derivedLinearOfCentral.{u,u,u} (algebraMap K B.A)
      (concentratedScalarCocycle K B hzero hd)
    (ConcentratedDGA.comparison B hzero hbot hd).equivalence.inverse.Linear K := by
  let := derivedLinearOfCentral.{u,u,u} (algebraMap K B.A)
    (concentratedScalarCocycle K B hzero hd)
  let : (ConcentratedDGA.comparison B hzero hbot hd).equivalence.functor.Linear K :=
    concentrated_functor_linear K B hzero hbot hd
  infer_instance

end Concentrated

#print axioms Beilinson.CentralDegreeZero.concentrated_inverse_linear
#print axioms Beilinson.CentralDegreeZero.concentrated_functor_linear
#print axioms Beilinson.CentralDegreeZero.localization_linear
#print axioms Beilinson.CentralDegreeZero.component_linear
#print axioms Beilinson.CentralDegreeZero.equivalence_functor_linear

end Beilinson.CentralDegreeZero

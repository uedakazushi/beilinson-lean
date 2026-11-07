module

public import Beilinson.DerivedDevissage
public import Beilinson.KroneckerResolution

/-! The finite-dimensional Kronecker resolution supplies the algebraic bounded
restriction: a bounded object with finite-dimensional cohomology lies in every
strictly full triangulated subcategory containing finite projective modules.
No identification with an externally defined perfect or compact subcategory is
assumed in this statement. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory

namespace Beilinson.KroneckerPerfect

universe u v w

variable {k : Type u} [Field k]
  [HasDerivedCategory.{w} (ModuleCat.{v} (Kronecker.Algebra k)ᵐᵒᵖ)]
  (P : ObjectProperty (DerivedCategory (ModuleCat.{v} (Kronecker.Algebra k)ᵐᵒᵖ)))
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- A finite module is assembled from two finite projective modules by the
short exact resolution, regarded as a distinguished triangle. -/
theorem finite_module_mem
    (hP : ∀ M : ModuleCat.{v} (Kronecker.Algebra k)ᵐᵒᵖ, Projective M →
      Kronecker.finiteRightModules M → P ((DerivedCategory.singleFunctor _ 0).obj M))
    (M : ModuleCat.{v} (Kronecker.Algebra k)ᵐᵒᵖ) (hM : Kronecker.finiteRightModules M) :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let S := Kronecker.rightModuleResolution M
  have hS : S.ShortExact := Kronecker.rightModuleResolution_shortExact M
  have hf := Kronecker.finite_rightModuleResolution_terms M hM
  exact P.ext_of_isTriangulatedClosed₃ hS.singleTriangle hS.singleTriangle_distinguished
    (hP S.X₁ inferInstance hf.1) (hP S.X₂ inferInstance hf.2)

/-- Bounded finite-dimensional cohomology is sufficient for membership in any
strictly full triangulated subcategory containing the finite projective modules. -/
theorem bounded_mem_of_finite_cohomology
    (hP : ∀ M : ModuleCat.{v} (Kronecker.Algebra k)ᵐᵒᵖ, Projective M →
      Kronecker.finiteRightModules M → P ((DerivedCategory.singleFunctor _ 0).obj M))
    (K : DerivedCategory (ModuleCat.{v} (Kronecker.Algebra k)ᵐᵒᵖ))
    (hK : (∃ a : ℤ, K.IsGE a) ∧ ∃ b : ℤ, K.IsLE b)
    (hH : ∀ i : ℤ, Kronecker.finiteRightModules
      ((DerivedCategory.homologyFunctor _ i).obj K)) : P K := by
  apply DerivedDevissage.of_isBounded P K hK
  intro i
  exact finite_module_mem P hP _ (hH i)

end Beilinson.KroneckerPerfect

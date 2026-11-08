module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Exact functors commute with changing the chosen target derived-category model. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StacksDraft.DerivedModel

namespace Beilinson.ExactFunctorModels

universe u v u' v' w z z'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (hC : HasDerivedCategory.{w} C)
variable (h₁ : HasDerivedCategory.{z} D) (h₂ : HasDerivedCategory.{z'} D)

/-- Derive an exact functor while specifying both localization models explicitly. -/
def map : @DerivedCategory C _ _ hC ⥤ @DerivedCategory D _ _ h₁ := by
  letI := hC
  letI := h₁
  exact F.mapDerivedCategory

def factors : @DerivedCategory.Q C _ _ hC ⋙ map F hC h₁ ≅
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ h₁ := by
  letI := hC
  letI := h₁
  exact F.mapDerivedCategoryFactors

/-- The square relating exact derived functors and a change of target model commutes. -/
def targetModelIso : map F hC h₁ ⋙ (modelEquiv h₁ h₂).functor ≅ map F hC h₂ := by
  letI := hC
  let A := F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ h₂
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) A
      (map F hC h₁ ⋙ (modelEquiv h₁ h₂).functor) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (factors F hC h₁) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (modelCompQIso h₁ h₂)⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) A (map F hC h₂) :=
    ⟨factors F hC h₂⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) A A
    (map F hC h₁ ⋙ (modelEquiv h₁ h₂).functor) (map F hC h₂) (Iso.refl _)

#print axioms targetModelIso

end Beilinson.ExactFunctorModels

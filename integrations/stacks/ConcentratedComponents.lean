module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra

/-! Ordinary complexes of homogeneous components of modules over a dg algebra
concentrated in degree zero, without first transporting the dg algebra by equality. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedAlgebra DifferentialGradedModule

namespace Beilinson.ConcentratedComponents

universe r b m
variable {R : Type r} [CommRing R] (B : DifferentialGradedAlgebra.{r,b} R)
variable (hzero : ∀ a : B.A, a ∈ B.grading 0) (hd : ∀ a : B.A, B.d a = 0)

/-- Degree-zero scalars preserve every homogeneous component. -/
@[instance_reducible]
def componentModule (M : DifferentialGradedModule.{r,b,m} B) (q : ℤ) :
    Module B.Aᵐᵒᵖ (M.grading q) := by
  letI : SMul B.Aᵐᵒᵖ (M.grading q) := ⟨fun a x =>
    ⟨a • (x : M.M), by simpa using M.smul_mem q 0 x a.unop x.property (hzero a.unop)⟩⟩
  exact Function.Injective.module B.Aᵐᵒᵖ (M.grading q).subtype.toAddMonoidHom
    Subtype.val_injective (fun _ _ => rfl)

/-- Bundle the coefficient structure so later maps use exactly the same module data. -/
def component (M : DifferentialGradedModule.{r,b,m} B) (q : ℤ) : ModuleCat.{m} B.Aᵐᵒᵖ := by
  letI := componentModule B hzero M q
  exact ModuleCat.of B.Aᵐᵒᵖ (M.grading q)

def differential (M : DifferentialGradedModule.{r,b,m} B) (q : ℤ) :
    component B hzero M q →ₗ[B.Aᵐᵒᵖ] component B hzero M (q + 1) where
  toFun := M.gradedDifferential q
  map_add' := map_add _
  map_smul' a x := by
    change M.grading q at x
    apply Subtype.ext
    change M.d (a • (x : M.M)) = a • M.d x
    simpa [hd] using M.leibniz q 0 x a.unop x.property (hzero a.unop)

def complex (M : DifferentialGradedModule.{r,b,m} B) :
    CochainComplex (ModuleCat.{m} B.Aᵐᵒᵖ) ℤ :=
  CochainComplex.of (component B hzero M)
    (fun q => ModuleCat.ofHom (X := component B hzero M q)
      (Y := component B hzero M (q + 1)) (differential B hzero hd M q)) (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change M.grading q at x
      apply Subtype.ext
      exact LinearMap.congr_fun M.d_comp_d x)

def map {M N : DifferentialGradedModule.{r,b,m} B} (f : M ⟶ N) :
    complex B hzero hd M ⟶ complex B hzero hd N :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom
    (X := component B hzero M q) (Y := component B hzero N q) {
    toFun := f.gradedMap q
    map_add' := map_add _
    map_smul' a x := by
      change M.grading q at x
      exact Subtype.ext (f.map_smul x a.unop) }) (fun q => by
      dsimp only [complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change M.grading q at x
      apply Subtype.ext
      exact (LinearMap.congr_fun f.map_d (x : M.M)).symm)

def functor : DifferentialGradedModule.{r,b,m} B ⥤
    CochainComplex (ModuleCat.{m} B.Aᵐᵒᵖ) ℤ where
  obj := complex B hzero hd
  map := map B hzero hd
  map_id M := by ext q x; rfl
  map_comp f g := by ext q x; rfl

#print axioms functor

/-- In the standard degree-zero model this is the existing component functor. -/
def standardIso (R : Type r) [CommRing R] (S : Type r) [Ring S] [Algebra R S] :
    functor (degreeZero R S) (fun a => by simp [degreeZero, degreeZeroGrading])
      (fun _ => rfl) ≅ degreeZeroComponentFunctor R Sᵐᵒᵖ := Iso.refl _

#print axioms standardIso

end Beilinson.ConcentratedComponents

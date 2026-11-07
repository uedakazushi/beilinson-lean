module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLinear
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsHomUnit
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic

/-! The linear identification Hom(O_X,M) = Gamma(X,M), with the base-scalar
structure explicit. This is input for the geometric endomorphism calculation. -/

set_option autoImplicit false

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace Beilinson.SheafHomSections

universe u

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The structure sheaf, explicitly in the scheme module category. -/
abbrev unitObject (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The linear Hom-to-sections map for an already chosen compatible linear structure. -/
def unitHomLinearMapOfLinear [Linear A X.Modules] [(globalSectionsOver f).Linear A]
    (M : X.Modules) : (unitObject X ⟶ M) →ₗ[A] (globalSectionsOver f).obj M where
  toFun g := (g.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))
  map_add' := by intros; rfl
  map_smul' a g := by
    change ((globalSectionsOver f).map (a • g)).hom
        (1 : X.ringCatSheaf.obj.obj (op ⊤)) = _
    rw [Functor.map_smul]
    rfl

/-- A version which reuses the caller's scalar data instead of expanding it in the result type. -/
def unitHomLinearEquivOfLinear [Linear A X.Modules] [(globalSectionsOver f).Linear A]
    (M : X.Modules) : (unitObject X ⟶ M) ≃ₗ[A] (globalSectionsOver f).obj M :=
  LinearEquiv.ofBijective (unitHomLinearMapOfLinear f M) (bijective_unitHom_app_top_one M)

/-- Evaluation at the global section 1, as a base-linear map. -/
def unitHomLinearMap (M : X.Modules) :
    letI := Scheme.linearOver f
    (unitObject X ⟶ M) →ₗ[A] (globalSectionsOver f).obj M := by
  let := Scheme.linearOver f
  exact
    { toFun := fun g => (g.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))
      map_add' := by intros; rfl
      map_smul' := by
        intro a g
        exact Scheme.smul_val_app_top X A ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom
          a g (1 : X.ringCatSheaf.obj.obj (op ⊤)) }

/-- The familiar Hom-to-sections bijection, with linearity rather than just an Equiv. -/
def unitHomLinearEquiv (M : X.Modules) :
    letI := Scheme.linearOver f
    (unitObject X ⟶ M) ≃ₗ[A] (globalSectionsOver f).obj M := by
  let := Scheme.linearOver f
  exact LinearEquiv.ofBijective (unitHomLinearMap f M) (bijective_unitHom_app_top_one M)

@[simp] theorem unitHomLinearEquiv_apply (M : X.Modules)
    (g : unitObject X ⟶ M) :
    unitHomLinearEquiv f M g =
      (g.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤)) := rfl

/-- The diagonal identity is normalized to 1. -/
@[simp] theorem unitHomLinearEquiv_id :
    unitHomLinearEquiv f (unitObject X) (𝟙 _) =
      (1 : X.ringCatSheaf.obj.obj (op ⊤)) := rfl

/-- The identification commutes with maps of the target sheaf. -/
theorem naturality {M N : X.Modules}
    (g : unitObject X ⟶ M) (h : M ⟶ N) :
    unitHomLinearEquiv f N (g ≫ h) =
      (globalSectionsOver f).map h (unitHomLinearEquiv f M g) := rfl

/-- Compare the scalar structure used by global sections with that of tensor functors. -/
theorem linearOver_eq_modulesLinear :
    Scheme.linearOver f = modulesLinear A (Over.mk f) := by
  rfl

#print axioms Beilinson.SheafHomSections.unitHomLinearEquivOfLinear
#print axioms Beilinson.SheafHomSections.unitHomLinearEquiv
#print axioms Beilinson.SheafHomSections.unitHomLinearEquiv_id
#print axioms Beilinson.SheafHomSections.naturality
#print axioms Beilinson.SheafHomSections.linearOver_eq_modulesLinear

end Beilinson.SheafHomSections

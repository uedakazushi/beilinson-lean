module

public import Beilinson.KroneckerPerfect
public import StacksFrontier.Homology.Perfect.Characterizing

/-! Apply the production finite-projective reconstruction to the actual Stacks
compact/perfect predicates. Compactness is equivalent to bounded finite-dimensional cohomology. The
geometric End identification remains separate. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.Perfect

attribute [local instance] isClosedUnderIsomorphisms_isCompactObject
  isTriangulated_isCompactObject

namespace Beilinson.KroneckerCompact

universe u

local instance moduleDerivedCategory (R : Type u) [Ring R] :
    HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _

local instance derivedCoproducts (R : Type u) [Ring R] :
    HasCoproducts.{u} (DerivedCategory (ModuleCat.{u} R)) :=
  fun J => hasCoproductsOfShape_derivedCategory J

/-- A finite projective module over any ring gives a compact object in degree zero. -/
theorem finite_projective_single_compact {R : Type u} [Ring R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] :
    IsCompactObject.{u} ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  apply (isPerfect_iff_isCompactObject _).mp
  let P := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  have hX (i : ℤ) : Nonempty (M ≃ₗ[R] P.X i) ∨ Subsingleton (P.X i) := by
    by_cases hi : i = 0
    · subst i
      let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm
      exact Or.inl ⟨LinearEquiv.ofBijective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom)⟩
    · exact Or.inr (ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi))
  refine ⟨P, 0, 0, inferInstance, inferInstance, fun i => ?_, fun i => ?_, ?_⟩
  · rcases hX i with ⟨⟨e⟩⟩ | _
    · exact Module.Finite.equiv e
    · infer_instance
  · rcases hX i with ⟨⟨e⟩⟩ | _
    · exact Module.Projective.of_equiv e
    · infer_instance
  · exact ⟨(DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M⟩

variable {k : Type u} [Field k]

attribute [local instance] Kronecker.groundModule

local instance groundTower (M : ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ) :
    IsScalarTower k (Kronecker.Algebra k)ᵐᵒᵖ M :=
  IsScalarTower.of_compHom k (Kronecker.Algebra k)ᵐᵒᵖ M

private theorem kronecker_projective_single_compact
    (M : ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ) (hP : Projective M)
    (hM : Kronecker.finiteRightModules M) :
    IsCompactObject.{u} ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let := hP
  let := Kronecker.groundModule (k := k) M
  let : IsScalarTower k (Kronecker.Algebra k)ᵐᵒᵖ M :=
    IsScalarTower.of_compHom k (Kronecker.Algebra k)ᵐᵒᵖ M
  let : Module.Finite k M := hM
  let : Module.Finite (Kronecker.Algebra k)ᵐᵒᵖ M :=
    Module.Finite.of_restrictScalars_finite k (Kronecker.Algebra k)ᵐᵒᵖ M
  exact finite_projective_single_compact M

/-- Every finite-dimensional right Kronecker module is compact in the derived category. -/
theorem finite_module_isCompact (M : ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ)
    (hM : Kronecker.finiteRightModules M) :
    IsCompactObject.{u} ((DerivedCategory.singleFunctor _ 0).obj M) :=
  KroneckerPerfect.finite_module_mem IsCompactObject
    kronecker_projective_single_compact M hM

/-- Bounded finite-dimensional cohomology implies compactness for right Kronecker complexes. -/
theorem bounded_finite_cohomology_isCompact
    (K : DerivedCategory (ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ))
    (hK : (∃ a : ℤ, K.IsGE a) ∧ ∃ b : ℤ, K.IsLE b)
    (hH : ∀ i : ℤ, Kronecker.finiteRightModules
      ((DerivedCategory.homologyFunctor _ i).obj K)) : IsCompactObject.{u} K :=
  KroneckerPerfect.bounded_mem_of_finite_cohomology IsCompactObject
    kronecker_projective_single_compact K hK hH

/-- The same sufficient condition, using the actual finite-projective-complex definition. -/
theorem bounded_finite_cohomology_isPerfect
    (K : DerivedCategory (ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ))
    (hK : (∃ a : ℤ, K.IsGE a) ∧ ∃ b : ℤ, K.IsLE b)
    (hH : ∀ i : ℤ, Kronecker.finiteRightModules
      ((DerivedCategory.homologyFunctor _ i).obj K)) : IsPerfect K :=
  (isPerfect_iff_isCompactObject K).mpr (bounded_finite_cohomology_isCompact K hK hH)

/-- The finite-dimensional algebra makes every perfect complex bounded with
finite-dimensional cohomology. No projective-dimension bound is needed for this direction. -/
theorem perfect_bounded_finite_cohomology
    (K : DerivedCategory (ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ)) (hK : IsPerfect K) :
    ((∃ a : ℤ, K.IsGE a) ∧ ∃ b : ℤ, K.IsLE b) ∧
      (∀ i : ℤ, Kronecker.finiteRightModules
        ((DerivedCategory.homologyFunctor _ i).obj K)) := by
  let R := (Kronecker.Algebra k)ᵐᵒᵖ
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e⟩⟩ := hK
  let := ha
  let := hb
  constructor
  · exact ⟨⟨a, DerivedCategory.TStructure.t.isGE_of_iso e.symm a⟩,
      ⟨b, DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩⟩
  · intro i
    have : Module.Finite R (P.X i) := hf i
    have : Module.Finite k (P.X i) := Module.Finite.trans (R := k) R (P.X i)
    have : Module.Finite k (P.cycles i) :=
      Module.Finite.of_injective ((P.iCycles i).hom.restrictScalars k)
        ((ModuleCat.mono_iff_injective (P.iCycles i)).mp inferInstance)
    have hfinite : Module.Finite k (P.homology i) :=
      Module.Finite.of_surjective ((P.homologyπ i).hom.restrictScalars k)
        ((ModuleCat.epi_iff_surjective (P.homologyπ i)).mp inferInstance)
    let F := ModuleCat.restrictScalars (algebraMap k R)
    let eH := F.mapIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P)
    let : Module.Finite k (F.obj
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj P)) := by
      change Module.Finite k (P.homology i)
      exact hfinite
    exact Module.Finite.of_surjective eH.inv.hom
      (ConcreteCategory.bijective_of_isIso eH.inv).2

/-- The complete algebraic finiteness criterion for right Kronecker complexes. -/
theorem compact_iff_bounded_finite_cohomology
    (K : DerivedCategory (ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ)) :
    IsCompactObject.{u} K ↔
      (((∃ a : ℤ, K.IsGE a) ∧ ∃ b : ℤ, K.IsLE b) ∧
        ∀ i : ℤ, Kronecker.finiteRightModules
          ((DerivedCategory.homologyFunctor _ i).obj K)) :=
  ⟨fun h => perfect_bounded_finite_cohomology K ((isPerfect_iff_isCompactObject K).mpr h),
    fun h => bounded_finite_cohomology_isCompact K h.1 h.2⟩

/-- Perfectness has exactly the same bounded finite-cohomology criterion. -/
theorem perfect_iff_bounded_finite_cohomology
    (K : DerivedCategory (ModuleCat.{u} (Kronecker.Algebra k)ᵐᵒᵖ)) :
    IsPerfect K ↔
      (((∃ a : ℤ, K.IsGE a) ∧ ∃ b : ℤ, K.IsLE b) ∧
        ∀ i : ℤ, Kronecker.finiteRightModules
          ((DerivedCategory.homologyFunctor _ i).obj K)) :=
  (isPerfect_iff_isCompactObject K).trans (compact_iff_bounded_finite_cohomology K)

#print axioms Beilinson.KroneckerCompact.perfect_iff_bounded_finite_cohomology
#print axioms Beilinson.KroneckerCompact.perfect_bounded_finite_cohomology
#print axioms Beilinson.KroneckerCompact.compact_iff_bounded_finite_cohomology
#print axioms Beilinson.KroneckerCompact.finite_projective_single_compact
#print axioms Beilinson.KroneckerCompact.finite_module_isCompact
#print axioms Beilinson.KroneckerCompact.bounded_finite_cohomology_isCompact
#print axioms Beilinson.KroneckerCompact.bounded_finite_cohomology_isPerfect

end Beilinson.KroneckerCompact

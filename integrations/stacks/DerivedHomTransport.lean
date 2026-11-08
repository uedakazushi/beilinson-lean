module

public import Beilinson.EndTransportYoneda
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorEquivalenceTransport

/-! Classical total derived Hom with its ordinary right endomorphism action,
and its natural compatibility with an exact equivalence of abelian categories. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Beilinson.DerivedHomTransport

universe u v w u' w' t

section Existence
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [IsGrothendieckAbelian.{v} C]
variable {D : Type u'} [Category.{t} D] [Abelian D] [HasDerivedCategory.{w'} D]

/-- Any additive functor out of a Grothendieck abelian category has a total
right derived functor, computed on K-injective resolutions. -/
theorem hasRightDerived (F : C ⥤ D) [F.Additive] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      _, _, 0, _, _, 0}
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (Stacks.Injectives.exists_kInjective_resolution_of_grothendieck (C := C))).1
  exact Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

end Existence

local instance moduleDerivedCategory (R : Type v) [Ring R] :
    HasDerivedCategory (ModuleCat.{v} R) := HasDerivedCategory.standard _

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{w} C]

local instance homHasRightDerived (E : C) :
    ((preadditiveCoyonedaObj E).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  hasRightDerived (preadditiveCoyonedaObj E)

/-- Classical RHom(E,-), derived from the ordinary right End(E)-module Hom functor. -/
def derivedHom (E : C) : DerivedCategory C ⥤ DerivedCategory (ModuleCat.{v} (End E)ᵐᵒᵖ) :=
  ((preadditiveCoyonedaObj E).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The canonical comparison of ordinary Hom with its classical right derived functor. -/
def derivedHomUnit (E : C) :
    (preadditiveCoyonedaObj E).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedHom E :=
  ((preadditiveCoyonedaObj E).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

instance derivedHom_isRightDerived (E : C) :
    (derivedHom E).IsRightDerivedFunctor (derivedHomUnit E)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [derivedHom, derivedHomUnit]
  infer_instance

/-- On a K-injective complex the canonical comparison is invertible, so RHom
is computed by applying the ordinary right-module Hom functor term by term. -/
instance derivedHomUnit_isIso (E : C) (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((derivedHomUnit E).app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) :=
  Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective _ _ (derivedHomUnit E) I

section Transport
variable (k : Type t) [CommRing k] [Linear k C]
variable {D : Type u'} [Category.{v} D] [Abelian D] [Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k] [F.IsEquivalence]
variable (E : C) {T : D} (e : F.obj E ≅ T)

/-- Change the actual right-module coefficient ring along the induced End isomorphism. -/
def coefficients : ModuleCat.{v} (End T)ᵐᵒᵖ ≌ ModuleCat.{v} (End E)ᵐᵒᵖ :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (RingEquiv.op (EndTransportYoneda.algebraEquiv k F E e).toRingEquiv)

instance coefficients_inverse_additive : (coefficients k F E e).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Ordinary Hom commutes with the equivalence, including the actual End action. -/
def underivedIso : preadditiveCoyonedaObj E ⋙ (coefficients k F E e).inverse ≅
    F ⋙ preadditiveCoyonedaObj T :=
  Functor.isoWhiskerRight (EndTransportYoneda.homFunctorIso k F E e) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (coefficients k F E e).unitIso.symm ≪≫
        Functor.rightUnitor _)

variable [IsGrothendieckAbelian.{v} D] [HasDerivedCategory.{w'} D]

/-- The classical, independently derived Hom functors commute with the equivalence
and coefficient change. Both right derived functors exist by K-injective resolutions. -/
def derivedIso : derivedHom E ⋙ (coefficients k F E e).inverse.mapDerivedCategory ≅
    F.mapDerivedCategory ⋙ derivedHom T :=
  Functor.totalRightDerivedMapHomotopyCompIsoOfEquivalence F
    (preadditiveCoyonedaObj E) (preadditiveCoyonedaObj T)
    (coefficients k F E e).inverse (underivedIso k F E e)

end Transport

#print axioms derivedIso
#print axioms derivedHom_isRightDerived
#print axioms derivedHomUnit_isIso
#print axioms hasRightDerived
#print axioms derivedHom

end Beilinson.DerivedHomTransport

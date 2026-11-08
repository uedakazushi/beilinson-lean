module

public import DerivedHomTransport
public import ExactFunctorModels

/-! Transport classical right derived functors while fixing both source models explicitly. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Beilinson.DerivedEquivalenceModels

universe u v u' v' t s t' s' w w' z z'
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
variable {B : Type t} [Category.{s} B] [Abelian B] [HasDerivedCategory.{z} B]
variable {B' : Type t'} [Category.{s'} B'] [Abelian B'] [HasDerivedCategory.{z'} B']

/-- Derive an additive functor in a specified source model. -/
def rightDerived (hC : HasDerivedCategory.{w} C) (P : C ⥤ B) [P.Additive] :
    @DerivedCategory C _ _ hC ⥤ DerivedCategory B := by
  letI := hC
  letI := DerivedHomTransport.hasRightDerived P
  exact (P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The two source model choices are data arguments, so coinciding category spellings
cannot cause instance search to silently use the same model on both sides. -/
def transport (hC : HasDerivedCategory.{w} C) (hD : HasDerivedCategory.{w'} D)
    (G : C ⥤ D) [G.Additive] [G.IsEquivalence]
    (P : C ⥤ B) (Q : D ⥤ B') [P.Additive] [Q.Additive]
    (H : B ⥤ B') [H.Additive] [H.IsEquivalence]
    (τ : P ⋙ H ≅ G ⋙ Q) :
    rightDerived hC P ⋙ H.mapDerivedCategory ≅
      ExactFunctorModels.map G hC hD ⋙ rightDerived hD Q := by
  letI := hC
  letI := hD
  letI := DerivedHomTransport.hasRightDerived P
  letI := DerivedHomTransport.hasRightDerived Q
  exact Functor.totalRightDerivedMapHomotopyCompIsoOfEquivalence G P Q H τ

#print axioms transport

end Beilinson.DerivedEquivalenceModels

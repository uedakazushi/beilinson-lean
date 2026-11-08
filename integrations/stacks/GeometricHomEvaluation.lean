module

public import Beilinson.CochainFromZero
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEndAlgebra

/-! Evaluate the actual geometric dg representable module at source degree zero.
The comparison respects its differential and its right endomorphism action. -/

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex.HomComplex
open Stacks.AlgebraicGeometry.Beilinson

namespace Beilinson.GeometricHomEvaluation

universe u
variable (A : Type u) [CommRing A] (n : ℕ)

abbrev representation := RingedSite.Rep.{u,u,u,u,u,0} (site A n) ℤ (generator A n)

variable (I : CochainComplex (RingedSite.TensorModO.{u,u,u,u,u} (site A n)) ℤ)

/-- The homogeneous part of the actual dg Hom module is ordinary Hom from E. -/
def evaluation (q : ℤ) :
    ((representation A n).functor.obj I).grading q ≃ₗ[ℤ] (generatorModule A n ⟶ I.X q) :=
  ((representation A n).moduleHom I q).trans
    (CochainFromZero.equiv ℤ (liftedGenerator A n) (liftedGeneratorXZeroIso A n).symm
      (fun _ hp => isZero_liftedGenerator_X A n hp) I q)

/-- The dg differential is the ordinary Hom-complex differential. -/
theorem differential (q : ℤ) (z : ((representation A n).functor.obj I).grading q) :
    evaluation A n I (q + 1)
      ⟨((representation A n).functor.obj I).d z,
        ((representation A n).functor.obj I).d_mem q z z.property⟩ =
      evaluation A n I q z ≫ I.d q (q + 1) := by
  change CochainFromZero.equiv ℤ (liftedGenerator A n) (liftedGeneratorXZeroIso A n).symm
    (fun _ hp => isZero_liftedGenerator_X A n hp) I (q + 1)
    ((representation A n).moduleHom I (q + 1) _) = _
  rw [(representation A n).module_d]
  exact CochainFromZero.differential ℤ (liftedGenerator A n) (liftedGeneratorXZeroIso A n).symm
    (fun _ hp => isZero_liftedGenerator_X A n hp) I q _

/-- The actual dg module action evaluates to precomposition by the explicit
geometric End(E) map. The existential records its homogeneous representative. -/
theorem action (q : ℤ) (z : ((representation A n).functor.obj I).grading q)
    (a : (endAlgebra A n).A) :
    ∃ c : ((representation A n).functor.obj I).grading q,
      c.val = MulOpposite.op a • z.val ∧
      evaluation A n I q c = (endAlgebraToEnd A n a).asHom ≫ evaluation A n I q z := by
  obtain ⟨c, hc, hcomp⟩ := (representation A n).module_action I q 0 q (add_zero q)
    z ⟨a, endAlgebra_mem_grading_zero A n a⟩
  refine ⟨c, hc, ?_⟩
  change CochainFromZero.equiv ℤ (liftedGenerator A n) (liftedGeneratorXZeroIso A n).symm
    (fun _ hp => isZero_liftedGenerator_X A n hp) I q ((representation A n).moduleHom I q c) = _
  rw [hcomp]
  exact CochainFromZero.precompose ℤ (liftedGenerator A n) (liftedGeneratorXZeroIso A n).symm
    (fun _ hp => isZero_liftedGenerator_X A n hp) I q _ _

/-- Homogeneous functorial maps evaluate to ordinary postcomposition. -/
theorem postcompose {J : CochainComplex (RingedSite.TensorModO.{u,u,u,u,u} (site A n)) ℤ}
    (f : I ⟶ J) (q : ℤ) (z : ((representation A n).functor.obj I).grading q) :
    ∃ c : ((representation A n).functor.obj J).grading q,
      c.val = ((representation A n).functor.map (Cochain.ofHom f)).1 z.val ∧
      evaluation A n J q c = evaluation A n I q z ≫ f.f q := by
  obtain ⟨c, hc, hcomp⟩ := (representation A n).map_comp I J 0 q q (zero_add q)
    (Cochain.ofHom f) z
  refine ⟨c, hc, ?_⟩
  change CochainFromZero.equiv ℤ (liftedGenerator A n) (liftedGeneratorXZeroIso A n).symm
    (fun _ hp => isZero_liftedGenerator_X A n hp) J q ((representation A n).moduleHom J q c) = _
  rw [hcomp]
  exact CochainFromZero.postcompose ℤ (liftedGenerator A n) (liftedGeneratorXZeroIso A n).symm
    (fun _ hp => isZero_liftedGenerator_X A n hp) f q _

#print axioms postcompose
#print axioms evaluation
#print axioms differential
#print axioms action

end Beilinson.GeometricHomEvaluation

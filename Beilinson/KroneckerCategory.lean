module

public import Beilinson.KroneckerModule
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# The category equivalence for the concrete Kronecker algebra

The target consists of two vector spaces and two maps from vertex 1 to vertex 0.
The source is mathlib's category of modules over the opposite algebra, i.e. right
modules with the composition convention used in the book.
-/

@[expose] public section

open CategoryTheory Module MulOpposite

universe u v

namespace Beilinson.Kronecker

variable (k : Type u) [Field k]

/-- A representation of the reverse Kronecker quiver. -/
structure ReverseRep where
  V₀ : ModuleCat.{v} k
  V₁ : ModuleCat.{v} k
  arrow : Fin 2 → V₁ →ₗ[k] V₀

namespace ReverseRep

variable {k}

/-- A pair of vertex maps commuting with the two arrows. -/
structure Hom (X Y : ReverseRep.{u,v} k) where
  zero : X.V₀ →ₗ[k] Y.V₀
  one : X.V₁ →ₗ[k] Y.V₁
  comm (i : Fin 2) : zero.comp (X.arrow i) = (Y.arrow i).comp one

@[ext] theorem hom_ext {X Y : ReverseRep.{u,v} k} {f g : Hom X Y}
    (h₀ : f.zero = g.zero) (h₁ : f.one = g.one) : f = g := by
  cases f
  cases g
  cases h₀
  cases h₁
  rfl

instance : Category (ReverseRep.{u,v} k) where
  Hom := Hom
  id X := ⟨LinearMap.id, LinearMap.id, fun _ => rfl⟩
  comp {X Y Z} f g := ⟨g.zero.comp f.zero, g.one.comp f.one, fun i => by
    ext m
    have hf := LinearMap.congr_fun (f.comm i) m
    have hg := LinearMap.congr_fun (g.comm i) (f.one m)
    exact (congrArg g.zero hf).trans hg⟩
  id_comp _ := by apply hom_ext <;> rfl
  comp_id _ := by apply hom_ext <;> rfl
  assoc _ _ _ := by apply hom_ext <;> rfl

end ReverseRep

/-- The canonical ground-field action on a bundled right module. -/
@[instance_reducible] def groundModule (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) : Module k M :=
  Module.compHom M (algebraMap k (Algebra k)ᵐᵒᵖ)

attribute [local instance] groundModule

local instance groundTower (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :
    IsScalarTower k (Algebra k)ᵐᵒᵖ M := IsScalarTower.of_compHom k (Algebra k)ᵐᵒᵖ M

variable {k}

/-- The two vertex spaces and reverse arrows of a right module. -/
def toReverseRep : ModuleCat.{v} (Algebra k)ᵐᵒᵖ ⥤ ReverseRep.{u,v} k where
  obj M :=
    { V₀ := ModuleCat.of k (vertex (actionOfModule (M := M)) (e₀ k))
      V₁ := ModuleCat.of k (vertex (actionOfModule (M := M)) (e₁ k))
      arrow := arrowMap (actionOfModule (M := M)) }
  map {M N} f :=
    { zero := vertexMap (actionOfModule (M := M)) (actionOfModule (M := N))
        (f.hom.restrictScalars k) (fun a m => f.hom.map_smul a m) (e₀ k)
      one := vertexMap (actionOfModule (M := M)) (actionOfModule (M := N))
        (f.hom.restrictScalars k) (fun a m => f.hom.map_smul a m) (e₁ k)
      comm := vertexMap_arrow _ _ _ _ }
  map_id M := by apply ReverseRep.hom_ext <;> rfl
  map_comp f g := by apply ReverseRep.hom_ext <;> rfl

/-- The right module constructed from a reverse-quiver representation. -/
def fromReverseRep : ReverseRep.{u,v} k ⥤ ModuleCat.{v} (Algebra k)ᵐᵒᵖ where
  obj X :=
    letI := moduleOfArrows X.arrow
    ModuleCat.of (Algebra k)ᵐᵒᵖ (X.V₀ × X.V₁)
  map {X Y} f := by
    letI := moduleOfArrows X.arrow
    letI := moduleOfArrows Y.arrow
    exact ModuleCat.ofHom
     { toFun := f.zero.prodMap f.one
       map_add' := map_add _
       map_smul' a m := (prodMap_intertwines_iff X.arrow Y.arrow f.zero f.one).mpr f.comm a m }
  map_id X := by
    let := moduleOfArrows X.arrow
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  map_comp {X Y Z} f g := by
    let := moduleOfArrows X.arrow
    let := moduleOfArrows Y.arrow
    let := moduleOfArrows Z.arrow
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

/-- The vertex decomposition is linear over the opposite algebra. -/
def moduleDecompose (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :
    M ≃ₗ[(Algebra k)ᵐᵒᵖ] fromReverseRep.obj (toReverseRep.obj M) where
  toEquiv := (decompose (actionOfModule (M := M))).toEquiv
  map_add' := (decompose (actionOfModule (M := M))).map_add
  map_smul' a m := decompose_action (actionOfModule (M := M)) a.unop m

/-- Naturality of the decomposition on right modules. -/
def moduleUnitIso : 𝟭 (ModuleCat.{v} (Algebra k)ᵐᵒᵖ) ≅ toReverseRep ⋙ fromReverseRep :=
  NatIso.ofComponents (fun M => (moduleDecompose M).toModuleIso) (fun {M N} f => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact decompose_intertwiner (actionOfModule (M := M)) (actionOfModule (M := N))
      (f.hom.restrictScalars k) (fun a m => f.hom.map_smul a m) m)

/-- Recover the original vertex-0 space after constructing a right module. -/
def recovered₀ (X : ReverseRep.{u,v} k) :
    (toReverseRep.obj (fromReverseRep.obj X)).V₀ ≃ₗ[k] X.V₀ where
  toFun m := m.val.1
  invFun x := ⟨(x, 0), by
    change ofArrows X.arrow (op (e₀ k)) (x, 0) = (x, 0)
    simp⟩
  left_inv m := by
    apply Subtype.ext
    have h := m.property
    change ofArrows X.arrow (op (e₀ k)) m.val = m.val at h
    exact (ofArrows_e₀ X.arrow m.val).symm.trans h
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change (ofArrows X.arrow (algebraMap k (Algebra k)ᵐᵒᵖ r) m.val).1 = r • m.val.1
    rw [(ofArrows X.arrow).commutes]
    rfl

/-- Recover the original vertex-1 space after constructing a right module. -/
def recovered₁ (X : ReverseRep.{u,v} k) :
    (toReverseRep.obj (fromReverseRep.obj X)).V₁ ≃ₗ[k] X.V₁ where
  toFun m := m.val.2
  invFun x := ⟨(0, x), by
    change ofArrows X.arrow (op (e₁ k)) (0, x) = (0, x)
    simp⟩
  left_inv m := by
    apply Subtype.ext
    have h := m.property
    change ofArrows X.arrow (op (e₁ k)) m.val = m.val at h
    exact (ofArrows_e₁ X.arrow m.val).symm.trans h
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change (ofArrows X.arrow (algebraMap k (Algebra k)ᵐᵒᵖ r) m.val).2 = r • m.val.2
    rw [(ofArrows X.arrow).commutes]
    rfl

/-- The recovered vertex spaces and arrows form the original representation. -/
def representationCounit (X : ReverseRep.{u,v} k) :
    toReverseRep.obj (fromReverseRep.obj X) ≅ X where
  hom :=
    { zero := (recovered₀ X).toLinearMap
      one := (recovered₁ X).toLinearMap
      comm i := by
        ext m
        change (ofArrows X.arrow (op (arrow k i)) m.val).1 = X.arrow i m.val.2
        exact congrArg Prod.fst (ofArrows_arrow X.arrow i m.val) }
  inv :=
    { zero := (recovered₀ X).symm.toLinearMap
      one := (recovered₁ X).symm.toLinearMap
      comm i := by
        ext m
        apply Subtype.ext
        change (X.arrow i m, 0) = ofArrows X.arrow (op (arrow k i)) (0, m)
        exact (ofArrows_arrow X.arrow i (0, m)).symm }
  hom_inv_id := by
    apply ReverseRep.hom_ext
    · apply LinearMap.ext; intro m; exact (recovered₀ X).symm_apply_apply m
    · apply LinearMap.ext; intro m; exact (recovered₁ X).symm_apply_apply m
  inv_hom_id := by
    apply ReverseRep.hom_ext
    · apply LinearMap.ext; intro m; exact (recovered₀ X).apply_symm_apply m
    · apply LinearMap.ext; intro m; exact (recovered₁ X).apply_symm_apply m

/-- Naturality of recovering the original reverse-quiver representation. -/
def representationCounitIso : fromReverseRep ⋙ toReverseRep ≅ 𝟭 (ReverseRep.{u,v} k) :=
  NatIso.ofComponents representationCounit (fun f => by
    apply ReverseRep.hom_ext <;> rfl)

/-- Right modules over the concrete Kronecker algebra are equivalent to
representations of the reverse Kronecker quiver. -/
def moduleEquivalence : ModuleCat.{v} (Algebra k)ᵐᵒᵖ ≌ ReverseRep.{u,v} k :=
  CategoryTheory.Equivalence.mk toReverseRep fromReverseRep moduleUnitIso representationCounitIso

/-- Right modules finite dimensional over the canonical ground-field action. -/
def finiteRightModules : ObjectProperty (ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :=
  fun M => FiniteDimensional k M

/-- Reverse representations with finite-dimensional spaces at both vertices. -/
def finiteReverseReps : ObjectProperty (ReverseRep.{u,v} k) :=
  fun X => FiniteDimensional k X.V₀ ∧ FiniteDimensional k X.V₁

instance : (finiteReverseReps (k := k)).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let : FiniteDimensional k X.V₀ := hX.1
    let : FiniteDimensional k X.V₁ := hX.2
    constructor
    · apply FiniteDimensional.of_surjective e.hom.zero
      intro y
      exact ⟨e.inv.zero y, LinearMap.congr_fun
        (congrArg ReverseRep.Hom.zero e.inv_hom_id) y⟩
    · apply FiniteDimensional.of_surjective e.hom.one
      intro y
      exact ⟨e.inv.one y, LinearMap.congr_fun
        (congrArg ReverseRep.Hom.one e.inv_hom_id) y⟩

/-- Finite dimensionality is exactly finite dimensionality at both vertices. -/
theorem finite_toReverseRep_iff (M : ModuleCat.{v} (Algebra k)ᵐᵒᵖ) :
    finiteReverseReps (toReverseRep.obj M) ↔ finiteRightModules M := by
  constructor
  · intro h
    let : FiniteDimensional k (vertex (actionOfModule (M := M)) (e₀ k)) := h.1
    let : FiniteDimensional k (vertex (actionOfModule (M := M)) (e₁ k)) := h.2
    exact (decompose (actionOfModule (M := M))).symm.finiteDimensional
  · intro h
    let : FiniteDimensional k M := h
    constructor
    · change FiniteDimensional k (vertex (actionOfModule (M := M)) (e₀ k))
      infer_instance
    · change FiniteDimensional k (vertex (actionOfModule (M := M)) (e₁ k))
      infer_instance

/-- The equivalence restricts to the full subcategories of finite-dimensional objects. -/
def finiteModuleEquivalence :
    (finiteRightModules (k := k)).FullSubcategory ≌
      (finiteReverseReps (k := k)).FullSubcategory :=
  (moduleEquivalence (k := k)).congrFullSubcategory (by
    funext M
    exact propext (finite_toReverseRep_iff M))

end Beilinson.Kronecker

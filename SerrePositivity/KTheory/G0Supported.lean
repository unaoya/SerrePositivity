module
public import SerrePositivity.KTheory.SupportedModule
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # The Grothendieck group of modules with closed support -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R]

/-- A short exact sequence certified in the ambient module category. -/
structure SupportedModuleShortExact (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) where
  left : SupportedFGModuleOn Z
  middle : SupportedFGModuleOn Z
  right : SupportedFGModuleOn Z
  f : left.obj →ₗ[R] middle.obj
  g : middle.obj →ₗ[R] right.obj
  injective : Function.Injective f
  exact : Function.Exact f g
  surjective : Function.Surjective g

variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
/-- Isomorphism and short exact sequence relations. -/
def g0SupportedRelations : Set (FreeAbelianGroup (SupportedFGModuleOn Z)) :=
  {a | ∃ X Y : SupportedFGModuleOn Z, Nonempty (X.obj ≅ Y.obj) ∧
    a = FreeAbelianGroup.of X - FreeAbelianGroup.of Y} ∪
  {a | ∃ T : SupportedModuleShortExact Z,
    a = FreeAbelianGroup.of T.middle - FreeAbelianGroup.of T.left -
      FreeAbelianGroup.of T.right}

abbrev G0WithSupport :=
  FreeAbelianGroup (SupportedFGModuleOn Z) ⧸ AddSubgroup.closure (g0SupportedRelations Z)

abbrev G0 (R : Type u) [CommRing R] :=
  G0WithSupport (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R))

namespace SupportedFGModuleOn
variable {Z}
/-- A canonical zero representative. -/
abbrev zero : SupportedFGModuleOn Z :=
  ⟨ModuleCat.of R PUnit, finiteModuleSupportedOn.of_subsingleton⟩

/-- A finite binary direct sum, represented by the product of modules. -/
abbrev directSum (X Y : SupportedFGModuleOn Z) : SupportedFGModuleOn Z :=
  ⟨ModuleCat.of R (X.obj × Y.obj),
    finiteModuleSupportedOn.of_exact (LinearMap.inl R X.obj Y.obj)
      (LinearMap.snd R X.obj Y.obj)
      (LinearMap.exact_iff.mpr (LinearMap.range_inl R X.obj Y.obj).symm)
      (LinearMap.snd_surjective) X.property Y.property⟩

/-- The split short exact sequence of a binary direct sum. -/
def directSumShortExact (X Y : SupportedFGModuleOn Z) : SupportedModuleShortExact Z where
  left := X
  middle := directSum X Y
  right := Y
  f := LinearMap.inl R X.obj Y.obj
  g := LinearMap.snd R X.obj Y.obj
  injective := LinearMap.inl_injective
  exact := LinearMap.exact_iff.mpr (LinearMap.range_inl R X.obj Y.obj).symm
  surjective := LinearMap.snd_surjective
end SupportedFGModuleOn

namespace G0WithSupport
variable {Z}
def mk (X : SupportedFGModuleOn Z) : G0WithSupport Z :=
  QuotientAddGroup.mk (FreeAbelianGroup.of X)

lemma mk_iso {X Y : SupportedFGModuleOn Z} (e : X.obj ≅ Y.obj) : mk X = mk Y := by
  unfold mk
  rw [QuotientAddGroup.eq, neg_add_eq_sub, ← neg_sub]
  exact AddSubgroup.neg_mem _
    (AddSubgroup.subset_closure (Or.inl ⟨X, Y, ⟨e⟩, rfl⟩))

lemma mk_shortExact (T : SupportedModuleShortExact Z) :
    mk T.middle = mk T.left + mk T.right := by
  unfold mk
  rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq]
  have h := AddSubgroup.neg_mem _ (AddSubgroup.subset_closure
    (k := g0SupportedRelations Z) (Or.inr ⟨T, rfl⟩))
  convert h using 1
  abel

/-- The universal additive evaluation. -/
def lift {B : Type*} [AddCommGroup B] (f : SupportedFGModuleOn Z → B)
    (hi : ∀ {X Y : SupportedFGModuleOn Z}, (X.obj ≅ Y.obj) → f X = f Y)
    (he : ∀ T : SupportedModuleShortExact Z, f T.middle = f T.left + f T.right) :
    G0WithSupport Z →+ B :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift f) (by
    rw [AddSubgroup.closure_le]
    rintro a (⟨X, Y, ⟨e⟩, rfl⟩ | ⟨T, rfl⟩)
    · simp [AddMonoidHom.mem_ker, FreeAbelianGroup.lift_apply_of, hi e]
    · simp [AddMonoidHom.mem_ker, FreeAbelianGroup.lift_apply_of, he T])

@[simp] lemma lift_mk {B : Type*} [AddCommGroup B] (f : SupportedFGModuleOn Z → B)
    (hi) (he) (X : SupportedFGModuleOn Z) : lift f hi he (mk X) = f X := by
  unfold lift mk
  exact (QuotientAddGroup.lift_mk _ _ _).trans (FreeAbelianGroup.lift_apply_of f X)

@[ext] lemma hom_ext {B : Type*} [AddCommGroup B] {f g : G0WithSupport Z →+ B}
    (h : ∀ X, f (mk X) = g (mk X)) : f = g := by
  ext X
  exact h X


@[simp] lemma mk_directSum (X Y : SupportedFGModuleOn Z) :
    mk (SupportedFGModuleOn.directSum X Y) = mk X + mk Y :=
  mk_shortExact (SupportedFGModuleOn.directSumShortExact X Y)

/-- A zero module has zero class, independent of its bundled representative. -/
lemma mk_of_subsingleton (X : SupportedFGModuleOn Z) [Subsingleton X.obj] : mk X = 0 := by
  let T : SupportedModuleShortExact Z :=
    { left := X, middle := X, right := X
      f := LinearMap.id, g := LinearMap.id
      injective := Function.injective_id
      exact := by intro x; simp [Subsingleton.elim x 0]
      surjective := Function.surjective_id }
  have h : mk X = mk X + mk X := mk_shortExact T
  have hh : mk X + 0 = mk X + mk X := by simpa using h
  exact (add_left_cancel hh).symm

@[simp] lemma mk_zero : mk (SupportedFGModuleOn.zero (Z := Z)) = 0 :=
  mk_of_subsingleton _

/-- A module supported on the empty set has zero class. -/
lemma mk_empty (X : SupportedFGModuleOn (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R))) :
    mk X = 0 := by
  have := (finiteModuleSupportedOn.bot_iff.mp X.property).2
  exact mk_of_subsingleton X

/-- The group with empty support is zero. -/
lemma eq_zero_of_empty_support
    (x : G0WithSupport (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R))) : x = 0 := by
  have h : AddMonoidHom.id
      (G0WithSupport (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R))) = 0 := by
    apply hom_ext
    intro X
    exact mk_empty X
  exact DFunLike.congr_fun h x

end G0WithSupport
end SerrePositivity

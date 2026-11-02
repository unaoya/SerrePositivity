module

public import SerrePositivity.CommutativeAlgebra.Support.Closed
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import SerrePositivity.CategoryTheory.AlternatingSum
public import SerrePositivity.CategoryTheory.Abelian.ShortComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Exact.Basic

/-! # 閉台を持つ有限生成加群とその G₀

## 概要

閉集合 Z に台を持つ有限生成加群の圏（射は元の ModuleCat の射）と、その短完全列による Grothendieck 群 `G0WithSupport Z` を定め、有界な台つき完全列の G₀ に値を取る Euler 加法性を示す。完全な加群の写像の、部分加群とその逆像・像への制限も与える。

## 方針

短完全列の関係式で G₀ を作る。任意の部分加群には Noether 性が要るが、有限生成な場合はそれだけで足りる。

## 規約

Mathlib には完全列による K₀（G₀）はない。Euler の加法性は CategoryTheory/Euler の一般論と並行していて、一本化は評価の定義域の一般化（区切り 1-4 以降）で行う。

## 使われ方

KTheory の G₀ の全体、PerfectComplex との比較、Paper。
-/

@[expose] public noncomputable section

universe u

section SupportedModulePart

namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R]

/-- Finite generation and closed support, as a property of ambient modules. -/
def finiteModuleSupportedOn (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    ObjectProperty (ModuleCat.{u} R) := fun M =>
  Module.Finite R M ∧ Module.support R M ⊆ Z

abbrev SupportedFGModuleOn (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :=
  (finiteModuleSupportedOn Z).FullSubcategory

instance {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (M : SupportedFGModuleOn Z) :
    Module.Finite R M.obj := M.property.1

namespace finiteModuleSupportedOn
variable {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
  {M N L : ModuleCat.{u} R}

lemma mono (h : finiteModuleSupportedOn Z M) (hZW : Z ≤ W) :
    finiteModuleSupportedOn W M := ⟨h.1, h.2.trans hZW⟩

lemma of_iso (e : M ≅ N) (h : finiteModuleSupportedOn Z M) :
    finiteModuleSupportedOn Z N := by
  have :=  h.1
  refine ⟨Module.Finite.of_surjective e.hom.hom e.toLinearEquiv.surjective, ?_⟩
  rw [← e.toLinearEquiv.support_eq]
  exact h.2

instance (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    (finiteModuleSupportedOn Z).IsClosedUnderIsomorphisms where
  of_iso e h := of_iso e h

lemma of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (h : finiteModuleSupportedOn Z M) : finiteModuleSupportedOn Z N := by
  have :=  h.1
  exact ⟨Module.Finite.of_surjective f hf,
    (Module.support_subset_of_surjective f hf).trans h.2⟩

lemma of_injective [IsNoetherianRing R] (f : M →ₗ[R] N)
    (hf : Function.Injective f) (h : finiteModuleSupportedOn Z N) :
    finiteModuleSupportedOn Z M := by
  have :=  h.1
  exact ⟨Module.Finite.of_injective f hf,
    (Module.support_subset_of_injective f hf).trans h.2⟩

lemma of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] L)
    (he : Function.Exact f g) (hg : Function.Surjective g)
    (hM : finiteModuleSupportedOn Z M) (hL : finiteModuleSupportedOn Z L) :
    finiteModuleSupportedOn Z N := by
  have :=  hM.1
  have :=  hL.1
  exact ⟨Module.Finite.of_exact he hg,
    (module_support_subset_union_of_exact f g he).trans (Set.union_subset hM.2 hL.2)⟩

lemma submodule [IsNoetherianRing R] (h : finiteModuleSupportedOn Z M)
    (U : Submodule R M) : finiteModuleSupportedOn Z (ModuleCat.of R U) :=
  of_injective U.subtype U.subtype_injective h

lemma quotient (h : finiteModuleSupportedOn Z M) (U : Submodule R M) :
    finiteModuleSupportedOn Z (ModuleCat.of R (M ⧸ U)) :=
  of_surjective U.mkQ U.mkQ_surjective h

lemma of_subsingleton [Module.Finite R M] [Subsingleton M] :
    finiteModuleSupportedOn Z M := by
  exact ⟨inferInstance, by simp [Module.support_eq_empty]⟩

lemma bot_iff : finiteModuleSupportedOn ⊥ M ↔ Module.Finite R M ∧ Subsingleton M := by
  simp only [finiteModuleSupportedOn, TopologicalSpace.Closeds.coe_bot,
    Set.subset_empty_iff, Module.support_eq_empty_iff]

lemma top_iff : finiteModuleSupportedOn ⊤ M ↔ Module.Finite R M := by
  simp [finiteModuleSupportedOn]

end finiteModuleSupportedOn

/-- Bundle a finite module with a proof of its support. -/
def supportedFGModuleOnObj (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (M : ModuleCat.{u} R) (h : finiteModuleSupportedOn Z M) : SupportedFGModuleOn Z :=
  ⟨M, h⟩

end SerrePositivity

end SupportedModulePart

section G0SupportedPart

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

end G0SupportedPart

section SupportedExactEulerPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}

namespace SupportedFGModuleOn
/-- The image of a map between finite supported modules remains finite and supported. -/
def image {M N : SupportedFGModuleOn Z} (f : M.obj ⟶ N.obj) : SupportedFGModuleOn Z :=
  ⟨Abelian.image f, finiteModuleSupportedOn.of_injective (Abelian.image.ι f).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) N.property⟩

/-- The coimage is a quotient of the finite supported source. -/
def coimage {M N : SupportedFGModuleOn Z} (f : M.obj ⟶ N.obj) : SupportedFGModuleOn Z :=
  ⟨Abelian.coimage f, finiteModuleSupportedOn.of_surjective (Abelian.coimage.π f).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) M.property⟩
end SupportedFGModuleOn

namespace G0WithSupport
omit [IsNoetherianRing R] in
lemma mk_of_isZero (M : SupportedFGModuleOn Z) (h : IsZero M.obj) : mk M = 0 := by
  have := ModuleCat.subsingleton_of_isZero h
  exact mk_of_subsingleton M

/-- Split an exact pair into the short exact sequence of its two images. -/
lemma mk_exact_images (X₁ X₂ X₃ : SupportedFGModuleOn Z)
    (f : X₁.obj ⟶ X₂.obj) (g : X₂.obj ⟶ X₃.obj) (he : Function.Exact f g) :
    mk X₂ = mk (SupportedFGModuleOn.image f) + mk (SupportedFGModuleOn.image g) := by
  let S := ModuleCat.shortComplexOfCompEqZero f.hom g.hom
    (LinearMap.ext he.apply_apply_eq_zero)
  have hS : S.Exact := ModuleCat.shortComplex_exact _ he
  let S'' := imageCoimageShortComplex S
  have hS'' : S''.ShortExact := imageCoimageShortComplex_shortExact hS
  let E : SupportedModuleShortExact Z :=
    { left := SupportedFGModuleOn.image f
      middle := X₂
      right := SupportedFGModuleOn.coimage g
      f := S''.f.hom
      g := S''.g.hom
      injective := (ModuleCat.mono_iff_injective _).mp hS''.mono_f
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS''.exact
      surjective := (ModuleCat.epi_iff_surjective _).mp hS''.epi_g }
  have h := mk_shortExact E
  change mk X₂ = mk (SupportedFGModuleOn.image f) + mk (SupportedFGModuleOn.coimage g) at h
  have hci : mk (SupportedFGModuleOn.coimage g) = mk (SupportedFGModuleOn.image g) :=
    mk_iso (Abelian.coimageIsoImage g)
  rw [hci] at h
  exact h
end G0WithSupport

/-- The Euler class of a sequence of finite supported modules. -/
def supportedModuleEuler (X : ℤ → SupportedFGModuleOn Z) : G0WithSupport Z :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤˣ) : ℤ) • G0WithSupport.mk (X i)

/-- A bounded supported long exact sequence gives G₀-valued Euler additivity. -/
lemma supportedModuleEuler_exact_sequence
    (X₁ X₂ X₃ : ℤ → SupportedFGModuleOn Z)
    (α : ∀ i, (X₁ i).obj ⟶ (X₂ i).obj) (β : ∀ i, (X₂ i).obj ⟶ (X₃ i).obj)
    (δ : ∀ i, (X₃ i).obj ⟶ (X₁ (i + 1)).obj)
    (h₂ : ∀ i, Function.Exact (α i) (β i))
    (h₃ : ∀ i, Function.Exact (β i) (δ i))
    (h₁ : ∀ i, Function.Exact (δ i) (α (i + 1)))
    (hb₂ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₂ i).obj)
    (hb₃ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₃ i).obj) :
    supportedModuleEuler X₂ = supportedModuleEuler X₁ + supportedModuleEuler X₃ := by
  let a := fun i => G0WithSupport.mk (SupportedFGModuleOn.image (α i))
  let b := fun i => G0WithSupport.mk (SupportedFGModuleOn.image (β i))
  let d := fun i => G0WithSupport.mk (SupportedFGModuleOn.image (δ i))
  have hfa : Function.HasFiniteSupport a := by
    obtain ⟨p, q, hpq⟩ := hb₂
    apply finiteSupport_of_bounded_zero a p q
    intro i hi
    exact G0WithSupport.mk_of_isZero _ (IsZero.of_mono (Abelian.image.ι (α i)) (hpq i hi))
  have hfb : Function.HasFiniteSupport b := by
    obtain ⟨p, q, hpq⟩ := hb₃
    apply finiteSupport_of_bounded_zero b p q
    intro i hi
    exact G0WithSupport.mk_of_isZero _ (IsZero.of_mono (Abelian.image.ι (β i)) (hpq i hi))
  have hfd : Function.HasFiniteSupport d := by
    obtain ⟨p, q, hpq⟩ := hb₃
    apply finiteSupport_of_bounded_zero d p q
    intro i hi
    exact G0WithSupport.mk_of_isZero _ (IsZero.of_epi (Abelian.factorThruImage (δ i)) (hpq i hi))
  have e₂ (i : ℤ) : G0WithSupport.mk (X₂ i) = a i + b i :=
    G0WithSupport.mk_exact_images _ _ _ (α i) (β i) (h₂ i)
  have e₃ (i : ℤ) : G0WithSupport.mk (X₃ i) = b i + d i :=
    G0WithSupport.mk_exact_images _ _ _ (β i) (δ i) (h₃ i)
  have e₁ (i : ℤ) : G0WithSupport.mk (X₁ i) = d (i - 1) + a i := by
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
    rw [add_sub_cancel_right]
    exact G0WithSupport.mk_exact_images _ _ _ (δ j) (α (j + 1)) (h₁ j)
  unfold supportedModuleEuler
  simp_rw [e₂, e₁, e₃]
  exact alternatingGroupFinsum_exact a b d hfa hfb hfd
end SerrePositivity

end SupportedExactEulerPart

section SubmoduleExactPart

namespace SerrePositivity
variable {R : Type*} [CommRing R]
  {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]

lemma submoduleRestriction_injective (U : Submodule R M₂) (f : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) :
    Function.Injective (f.restrict (p := U.comap f) (q := U) (fun _ h => h)) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

lemma submoduleImage_restrict_surjective (U : Submodule R M₂) (g : M₂ →ₗ[R] M₃) :
    Function.Surjective
      (g.restrict (p := U) (q := U.map g) (fun _ h => Submodule.mem_map_of_mem h)) := by
  rintro ⟨n, hn⟩
  obtain ⟨m, hm, he⟩ := Submodule.mem_map.mp hn
  exact ⟨⟨m, hm⟩, Subtype.ext he⟩

/-- No finite generation, Noetherian hypothesis, or surjectivity onto M₃ is needed. -/
lemma submoduleRestriction_exact (U : Submodule R M₂)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (he : Function.Exact f g) :
    Function.Exact (f.restrict (p := U.comap f) (q := U) (fun _ h => h))
      (g.restrict (p := U) (q := U.map g) (fun _ h => Submodule.mem_map_of_mem h)) := by
  intro n
  constructor
  · intro hn
    have hn' : g (n : M₂) = 0 := congrArg Subtype.val hn
    obtain ⟨m, hm⟩ := (he (n : M₂)).mp hn'
    exact ⟨⟨m, by change f m ∈ U; rw [hm]; exact n.property⟩, Subtype.ext hm⟩
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    exact he.apply_apply_eq_zero m

end SerrePositivity

end SubmoduleExactPart

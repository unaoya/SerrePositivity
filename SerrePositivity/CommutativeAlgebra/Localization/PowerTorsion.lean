module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Ideal.Maps

/-! # 局所化で消える元と一様な冪による零化

## 概要

乗法的集合 S による局所化で 0 になる有限生成加群の元は、S のある一つの元で零化される（一様な冪）。局所化の比較写像の核と余核の冪ねじれの評価、分母払いによる局所化の逆写像の持ち上げ、主局所化 R[1/g] の有限被覆の分子の取り戻しを与える。

## 方針

局所化で消えることは Mathlib の `IsLocalizedModule` の `exists_of_eq` 系で一つの分母の存在に言い換え、有限生成なら生成元ごとの分母の積をとる。ねじれは Mathlib の `Module.IsTorsion'` で書く（以前の `IsModuleSTorsion` は廃止）。

## 規約

`exists_uniform_pow_smul_zero` は主局所化の版の名前として残す（CLMST が使う）。

## 使われ方

共通模型（`Localization/CommonModel`）、主局所化（`Localization/Away`）、KTheory の G₀ の局所化、CLMST の比較の評価。
-/

@[expose] public noncomputable section

universe u

section LocalizationPowerBoundPart

namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 有限生成加群の各元をgのある冪が消せば、一つの共通冪が全加群を消す。 -/
theorem exists_uniform_pow_smul_zero [Module.Finite R M] (g : R)
    (h : ∀ x : M, ∃ n : ℕ, g ^ n • x = 0) :
    ∃ n : ℕ, ∀ x : M, g ^ n • x = 0 := by
  classical
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' R M
  let b := Pi.basisFun R (Fin r)
  choose n hn using fun i : Fin r ↦ h (f (b i))
  let N := Finset.univ.sup n
  have hzero : g ^ N • f = 0 := by
    apply b.ext
    intro i
    change g ^ N • f (b i) = 0
    have hi : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    rw [show N = (N - n i) + n i by omega, pow_add, mul_smul, hn i, smul_zero]
  refine ⟨N, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := hf x
  change (g ^ N • f) y = 0
  rw [hzero]
  rfl

/-- 主元局所化で零になる一つの元は、その元の冪で消える。 -/
theorem exists_pow_smul_zero_of_localized_zero (g : R) (x : M)
    (hx : LocalizedModule.mkLinearMap (Submonoid.powers g) M x = 0) :
    ∃ n : ℕ, g ^ n • x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M)).mp hx
  exact ⟨n, hn⟩

/-- 主元局所化で誘導される加群写像。 -/
abbrev awayModuleMap {N : Type*} [AddCommGroup N] [Module R N]
    (g : R) (f : M →ₗ[R] N) :=
  IsLocalizedModule.map (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) N) f

/-- 局所化した写像が全射なら、余核の各元はg冪ねじれである。 -/
theorem exists_pow_smul_mem_range_of_away_surjective
    {N : Type*} [AddCommGroup N] [Module R N] (g : R) (f : M →ₗ[R] N)
    (hf : Function.Surjective (awayModuleMap g f)) (y : N) :
    ∃ n : ℕ, g ^ n • y ∈ LinearMap.range f := by
  let ιM := LocalizedModule.mkLinearMap (Submonoid.powers g) M
  let ιN := LocalizedModule.mkLinearMap (Submonoid.powers g) N
  obtain ⟨z, hz⟩ := hf (ιN y)
  obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj ιM g z
  have heq : ιN (g ^ n • y - f x) = 0 := by
    rw [map_sub, map_smul]
    have hh := congrArg (awayModuleMap g f) hx
    change g ^ n • ιN y - ιN (f x) = 0
    change awayModuleMap g f (g ^ n • z) = awayModuleMap g f (ιM x) at hh
    simpa only [map_smul, hz, ιM, ιN, awayModuleMap,
      IsLocalizedModule.map_apply, sub_eq_zero] using hh
  obtain ⟨k, hk⟩ := exists_pow_smul_zero_of_localized_zero g _ heq
  refine ⟨k + n, ?_⟩
  refine ⟨g ^ k • x, ?_⟩
  rw [map_smul]
  rw [smul_sub, sub_eq_zero] at hk
  simpa only [pow_add, mul_smul] using hk.symm

/-- 有限生成な余核のg冪ねじれには一様な指数が存在する。 -/
theorem exists_uniform_pow_smul_coker_zero_of_away_surjective
    {N : Type*} [AddCommGroup N] [Module R N]
    (g : R) (f : M →ₗ[R] N) [Module.Finite R (N ⧸ LinearMap.range f)]
    (hf : Function.Surjective (awayModuleMap g f)) :
    ∃ n : ℕ, ∀ x : N ⧸ LinearMap.range f, g ^ n • x = 0 := by
  apply exists_uniform_pow_smul_zero g
  intro x
  obtain ⟨y, rfl⟩ := (LinearMap.range f).mkQ_surjective x
  obtain ⟨n, hn⟩ := exists_pow_smul_mem_range_of_away_surjective g f hf y
  refine ⟨n, ?_⟩
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr hn

end SerrePositivity

end LocalizationPowerBoundPart

section LocalizationComparisonBoundsPart

namespace SerrePositivity
variable {R M N T : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup T] [Module R T]

/-- A pointwise power bound on a finite module has one exponent for the entire module. -/
theorem exists_uniform_power_smul_eq_zero_of_finite [Module.Finite R M]
    (d : R) (h : ∀ x : M, ∃ n : ℕ, d ^ n • x = 0) :
    ∃ n : ℕ, ∀ x : M, d ^ n • x = 0 := by
  classical
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  choose k hk using fun j : Fin m => h (s j)
  let n := ∑ j, k j
  let l : M →ₗ[R] M := d ^ n • LinearMap.id
  have hgen : ∀ x ∈ Set.range s, x ∈ l.ker := by
    rintro _ ⟨j, rfl⟩
    change d ^ n • s j = 0
    have hj : k j ≤ n := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    calc
      d ^ n • s j = d ^ (n - k j) • (d ^ k j • s j) := by
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel hj]
      _ = 0 := by rw [hk, smul_zero]
  have hfull : (⊤ : Submodule R M) ≤ l.ker := by
    rw [← hs]
    exact Submodule.span_le.mpr hgen
  exact ⟨n, fun x => hfull (Submodule.mem_top)⟩

/-- The kernel of a comparison into its actual localization is pointwise power torsion. -/
theorem localizationComparison_ker_power_torsion
    (d : R) (f : M →ₗ[R] N) (l : M →ₗ[R] T) (v : N →ₗ[R] T)
    [IsLocalizedModule (.powers d) l] (hcomp : v.comp f = l)
    (x : M) (hx : f x = 0) : ∃ n : ℕ, d ^ n • x = 0 := by
  have hxl : l x = 0 := by
    rw [← hcomp, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (.powers d) l).mp hxl
  obtain ⟨n, hn⟩ := s.2
  change d ^ n = (s : R) at hn
  change (s : R) • x = 0 at hs
  exact ⟨n, by simpa only [← hn] using hs⟩

/-- A finite target embedded in the same localization has a uniformly power-annihilated cokernel. -/
theorem localizationComparison_exists_pow_annihilates_coker [Module.Finite R N]
    (d : R) (f : M →ₗ[R] N) (l : M →ₗ[R] T) (v : N →ₗ[R] T)
    [IsLocalizedModule (.powers d) l] (hv : Function.Injective v) (hcomp : v.comp f = l) :
    ∃ n : ℕ, ∀ y : N ⧸ f.range, d ^ n • y = 0 := by
  apply exists_uniform_power_smul_eq_zero_of_finite d
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective f.range y
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (.powers d) l (v y)
  have he : (s : R) • y = f x := by
    apply hv
    rw [map_smul]
    rw [← LinearMap.comp_apply, hcomp]
    exact hs
  obtain ⟨n, hn⟩ := s.2
  change d ^ n = (s : R) at hn
  refine ⟨n, ?_⟩
  rw [← map_smul]
  have he' : d ^ n • y = f x := by rw [hn]; exact he
  rw [he']
  exact (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨x, rfl⟩

/-- If both comparison maps give the same localization, the cokernel is
pointwise power torsion. The map out of the target need not be injective. -/
theorem localizationComparison_coker_power_torsion_of_localized_target
    (d : R) (f : M →ₗ[R] N) (l : M →ₗ[R] T) (v : N →ₗ[R] T)
    [IsLocalizedModule (.powers d) l] [IsLocalizedModule (.powers d) v]
    (hcomp : v.comp f = l) (y : N ⧸ f.range) :
    ∃ n : ℕ, d ^ n • y = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective f.range y
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (.powers d) l (v y)
  change (s : R) • v y = l x at hs
  have he : v ((s : R) • y - f x) = 0 := by
    rw [map_sub, map_smul]
    rw [show v (f x) = l x from LinearMap.congr_fun hcomp x, hs, sub_self]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (.powers d) v).mp he
  have he' : ((t : R) * (s : R)) • y = f ((t : R) • x) := by
    change (t : R) • ((s : R) • y - f x) = 0 at ht
    rw [smul_sub, sub_eq_zero, ← map_smul, smul_smul] at ht
    exact ht
  obtain ⟨n, hn⟩ := (t * s).2
  change d ^ n = (t : R) * (s : R) at hn
  refine ⟨n, ?_⟩
  rw [← map_smul, hn, he']
  exact (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨_, rfl⟩

/-- A finite common model has one cokernel exponent even when its map into the
localization has a nonzero power-torsion kernel. -/
theorem localizationComparison_exists_pow_annihilates_coker_of_localized_target
    [Module.Finite R N]
    (d : R) (f : M →ₗ[R] N) (l : M →ₗ[R] T) (v : N →ₗ[R] T)
    [IsLocalizedModule (.powers d) l] [IsLocalizedModule (.powers d) v]
    (hcomp : v.comp f = l) :
    ∃ n : ℕ, ∀ y : N ⧸ f.range, d ^ n • y = 0 :=
  exists_uniform_power_smul_eq_zero_of_finite d
    (localizationComparison_coker_power_torsion_of_localized_target d f l v hcomp)

/-- Two comparisons into one finite target have one common cokernel exponent. -/
theorem localizationComparisons_exists_common_pow_annihilates_cokers
    {M' : Type u} [AddCommGroup M'] [Module R M'] [Module.Finite R N]
    (d : R) (f : M →ₗ[R] N) (f' : M' →ₗ[R] N)
    (l : M →ₗ[R] T) (l' : M' →ₗ[R] T) (v : N →ₗ[R] T)
    [IsLocalizedModule (.powers d) l] [IsLocalizedModule (.powers d) l']
    (hv : Function.Injective v) (hcomp : v.comp f = l) (hcomp' : v.comp f' = l') :
    ∃ n : ℕ, (∀ y : N ⧸ f.range, d ^ n • y = 0) ∧
      (∀ y : N ⧸ f'.range, d ^ n • y = 0) := by
  obtain ⟨n, hn⟩ := localizationComparison_exists_pow_annihilates_coker d f l v hv hcomp
  obtain ⟨m, hm⟩ := localizationComparison_exists_pow_annihilates_coker d f' l' v hv hcomp'
  refine ⟨n + m, ?_, ?_⟩
  · intro y
    rw [add_comm n m, pow_add, mul_smul, hn, smul_zero]
  · intro y
    rw [pow_add, mul_smul, hm, smul_zero]

/-- Two maps to a finite common model admit a single cokernel exponent using
only the three localization structures, without an embedding of the model. -/
theorem localizationComparisons_exists_common_pow_annihilates_cokers_of_localized_target
    {M' : Type u} [AddCommGroup M'] [Module R M'] [Module.Finite R N]
    (d : R) (f : M →ₗ[R] N) (f' : M' →ₗ[R] N)
    (l : M →ₗ[R] T) (l' : M' →ₗ[R] T) (v : N →ₗ[R] T)
    [IsLocalizedModule (.powers d) l] [IsLocalizedModule (.powers d) l']
    [IsLocalizedModule (.powers d) v]
    (hcomp : v.comp f = l) (hcomp' : v.comp f' = l') :
    ∃ n : ℕ, (∀ y : N ⧸ f.range, d ^ n • y = 0) ∧
      (∀ y : N ⧸ f'.range, d ^ n • y = 0) := by
  obtain ⟨n, hn⟩ :=
    localizationComparison_exists_pow_annihilates_coker_of_localized_target d f l v hcomp
  obtain ⟨m, hm⟩ :=
    localizationComparison_exists_pow_annihilates_coker_of_localized_target d f' l' v hcomp'
  refine ⟨n + m, ?_, ?_⟩
  · intro y
    rw [add_comm n m, pow_add, mul_smul, hn, smul_zero]
  · intro y
    rw [pow_add, mul_smul, hm, smul_zero]

end SerrePositivity

end LocalizationComparisonBoundsPart

section LocalizationTorsionPart

namespace SerrePositivity
open scoped TensorProduct
variable {R : Type u} [CommRing R] {P : Submonoid R} {M N L : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]

/-! 乗法的集合 `P` についてのねじれは Mathlib の `Module.IsTorsion' M P` で表す（以前の `IsModuleSTorsion P M` は廃止した）。 -/

/-- `P` ねじれは、各元が `P` のある元で消えることと同じ。 -/
lemma isTorsion'_iff_forall : Module.IsTorsion' M P ↔ ∀ m : M, ∃ r ∈ P, r • m = 0 := by
  constructor
  · intro h m
    obtain ⟨r, hr⟩ := h (x := m)
    exact ⟨r.val, r.property, hr⟩
  · intro h m
    obtain ⟨r, hr, he⟩ := h m
    exact ⟨⟨r, hr⟩, he⟩

/-- `P` ねじれは、`P` での局所化が零になることと同じ。 -/
lemma isTorsion'_iff_subsingleton_localizedModule :
    Module.IsTorsion' M P ↔ Subsingleton (LocalizedModule P M) :=
  isTorsion'_iff_forall.trans LocalizedModule.subsingleton_iff.symm

/-- `P` ねじれは、局所化 `B` とのテンソル積が零になることと同じ。 -/
lemma isTorsion'_iff_subsingleton_tensor (B : Type u) [CommRing B] [Algebra R B] [IsLocalization P B] :
    Module.IsTorsion' M P ↔ Subsingleton (B ⊗[R] M) :=
  isTorsion'_iff_forall.trans (IsLocalizedModule.subsingleton_iff P (TensorProduct.mk R B M 1)).symm

/-- 完全列 `M → N → L` の両端が `P` ねじれなら中央も `P` ねじれ。 -/
lemma isTorsion'_of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] L) (he : Function.Exact f g)
    (hM : Module.IsTorsion' M P) (hL : Module.IsTorsion' L P) : Module.IsTorsion' N P := by
  rw [isTorsion'_iff_forall] at hM hL ⊢
  intro n
  obtain ⟨r, hr, er⟩ := hL (g n)
  have hk : g (r • n) = 0 := by simpa using er
  obtain ⟨m, hm⟩ := (he (r • n)).mp hk
  obtain ⟨s, hs, es⟩ := hM m
  refine ⟨s * r, P.mul_mem hs hr, ?_⟩
  rw [mul_smul, ← hm, ← map_smul, es, map_zero]

/-- 有限生成な `P` ねじれ加群は `P` の一つの元で零化される。 -/
lemma exists_annihilating_mem_of_isTorsion' [Module.Finite R M] (h : Module.IsTorsion' M P) :
    ∃ r ∈ P, ∀ m : M, r • m = 0 := by
  classical
  rw [isTorsion'_iff_forall] at h
  have hfin : ∀ t : Finset M, ∃ r ∈ P, ∀ m ∈ t, r • m = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, P.one_mem, by simp⟩
    | @insert m t hm ih =>
      obtain ⟨r, hr, er⟩ := h m
      obtain ⟨s, hs, es⟩ := ih
      refine ⟨s * r, P.mul_mem hs hr, ?_⟩
      intro n hn
      rcases Finset.mem_insert.mp hn with rfl | hn
      · simp [mul_smul, er]
      · rw [mul_comm, mul_smul, es n hn, smul_zero]
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R) (M := M)
  obtain ⟨r, hr, er⟩ := hfin t
  refine ⟨r, hr, fun m => ?_⟩
  have hm : m ∈ Submodule.span R (t : Set M) := by rw [ht]; trivial
  induction hm using Submodule.span_induction with
  | mem m hm => exact er m hm
  | zero => exact smul_zero r
  | add m n hm hn em en => simp [smul_add, em, en]
  | smul a m hm em => rw [smul_comm, em, smul_zero]

end SerrePositivity

end LocalizationTorsionPart

section LocalizationInversePart

namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 有限自由な始域を持つ局所化上の写像には、共通の分母を払った持ち上げがある。 -/
theorem exists_clear_denominators (g : R) (r : ℕ)
    (u : LocalizedModule (Submonoid.powers g) (Fin r → R) →ₗ[R]
      LocalizedModule (Submonoid.powers g) M) :
    ∃ (k : ℕ) (ψ : (Fin r → R) →ₗ[R] M), awayModuleMap g ψ = g ^ k • u := by
  classical
  let ιM := LocalizedModule.mkLinearMap (Submonoid.powers g) M
  let ιF := LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin r → R)
  let b := Pi.basisFun R (Fin r)
  choose n x hx using fun i : Fin r ↦
    IsLocalizedModule.Away.surj ιM g (u (ιF (b i)))
  let k := Finset.univ.sup n
  let ψ := b.constr R (fun i ↦ g ^ (k - n i) • x i)
  refine ⟨k, ψ, ?_⟩
  apply IsLocalizedModule.ext (Submonoid.powers g) ιF
    (IsLocalizedModule.map_units ιM)
  apply b.ext
  intro i
  change awayModuleMap g ψ (ιF (b i)) = g ^ k • u (ιF (b i))
  rw [show awayModuleMap g ψ (ιF (b i)) = ιM (ψ (b i)) from
    IsLocalizedModule.map_apply _ _ _ _ _]
  rw [show ψ (b i) = g ^ (k - n i) • x i from b.constr_basis R _ i, map_smul, ← hx i]
  have hi : n i ≤ k := Finset.le_sup (Finset.mem_univ i)
  rw [smul_smul, ← pow_add, Nat.sub_add_cancel hi]

/-- 局所化同型の逆写像を、g冪倍して元の加群上へ持ち上げる。 -/
theorem exists_away_inverse (g : R) (r : ℕ) (f : M →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ (k : ℕ) (ψ : (Fin r → R) →ₗ[R] M),
      awayModuleMap g ψ =
        g ^ k • (LinearEquiv.ofBijective (awayModuleMap g f) hf).symm.toLinearMap ∧
      Function.Bijective (awayModuleMap g ψ) := by
  let e := LinearEquiv.ofBijective (awayModuleMap g f) hf
  obtain ⟨k, ψ, hψ⟩ := exists_clear_denominators g r e.symm.toLinearMap
  refine ⟨k, ψ, hψ, ?_⟩
  rw [hψ]
  let ιM := LocalizedModule.mkLinearMap (Submonoid.powers g) M
  have hu := IsLocalizedModule.map_units ιM (⟨g ^ k, k, rfl⟩ : Submonoid.powers g)
  have hb := (Module.End.isUnit_iff _).mp hu
  exact hb.comp e.symm.bijective

end SerrePositivity

end LocalizationInversePart

section PrincipalCoverNumeratorsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity

/-- The original g times the chosen numerators of a cover of R[1/g] generate an
ideal containing a power of g. No regularity or nonzero condition on g is required. -/
theorem exists_pow_mem_span_scaled_cover_numerators
    {R : Type u} [CommRing R] (g : R) (t : Finset (Localization.Away g))
    (ht : Ideal.span (t : Set (Localization.Away g)) = ⊤) :
    ∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun x : t =>
      g * (IsLocalization.Away.sec g x.1).1)) := by
  let L := Localization.Away g
  let J : Ideal R := Ideal.span (Set.range (fun x : t =>
    g * (IsLocalization.Away.sec g x.1).1))
  have hmap : J.map (algebraMap R L) = ⊤ := by
    apply top_unique
    rw [← ht]
    apply Ideal.span_le.mpr
    intro x hx
    let u := IsLocalization.Away.sec g x
    have heq : algebraMap R L (g * u.1) = (algebraMap R L g) ^ (u.2 + 1) * x := by
      dsimp only [u]
      rw [map_mul, ← IsLocalization.Away.sec_spec g x, map_pow, pow_succ]
      ac_rfl
    apply ((J.map (algebraMap R L)).unit_mul_mem_iff_mem
      ((IsLocalization.Away.algebraMap_isUnit (S := L) g).pow (u.2 + 1))).mp
    rw [← heq]
    exact Ideal.mem_map_of_mem (algebraMap R L) (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩)
  have hone : algebraMap R L (1 : R) ∈ J.map (algebraMap R L) := by
    rw [hmap]
    trivial
  obtain ⟨m, hm, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers g) L J 1).mp hone
  obtain ⟨N, rfl⟩ := hm
  exact ⟨N, by simpa only [mul_one] using hmem⟩

/-- Local uniform annihilators on a finite cover give one exponent for the entire
module family. The family and its modules need not be finite or finitely generated. -/
theorem exists_uniform_family_pow_smul_zero_of_cover
    {R : Type u} [CommRing R] {ι : Type*} (X : ι → Type u)
    [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] (g : R) (t : Finset R)
    (hcover : ∃ k : ℕ, g ^ k ∈ Ideal.span (t : Set R))
    (hzero : ∀ a ∈ t, ∃ N : ℕ, ∀ i, ∀ x : X i, a ^ N • x = 0) :
    ∃ N : ℕ, ∀ i, ∀ x : X i, g ^ N • x = 0 := by
  let J : Ideal R := ⨅ i, Module.annihilator R (X i)
  have hspan : Ideal.span (t : Set R) ≤ J.radical := by
    apply Ideal.span_le.mpr
    intro a ha
    obtain ⟨N, hN⟩ := hzero a ha
    apply Ideal.mem_radical_iff.mpr
    refine ⟨N, ?_⟩
    change a ^ N ∈ ⨅ i, Module.annihilator R (X i)
    simp only [Submodule.mem_iInf]
    intro i
    exact Module.mem_annihilator.mpr (hN i)
  obtain ⟨k, hk⟩ := hcover
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp (Ideal.mem_radical_of_pow_mem (hspan hk))
  refine ⟨N, ?_⟩
  change g ^ N ∈ ⨅ i, Module.annihilator R (X i) at hN
  simp only [Submodule.mem_iInf] at hN
  intro i
  exact Module.mem_annihilator.mp (hN i)

end SerrePositivity

end PrincipalCoverNumeratorsPart

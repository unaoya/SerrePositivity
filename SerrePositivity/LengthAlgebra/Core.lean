module

public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.RingTheory.Length
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Category
public import SerrePositivity.CategoryTheory.Abelian.SerreLength
public import SerrePositivity.CategoryTheory.Euler
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.Algebra.Homology.HomologySequence

/-! # 正規化長さとその Serre 商

## 概要

論文 Lemma 2.3 と §3.4 の「正規化長さ」を抽象化した構造 `NormalizedLength C J`（イデアル J の冪で消える C 加群に ℝ≥0∞ の値を対応させ、零加群で 0、同型で不変、短完全列で加法的な関数）を定める。有限な冪ねじれ加群を零長さの加群で割った Serre 商に忠実な実数値の長さを降ろし、全ての冪ねじれ加群の商には拡大実数値の長さを降ろす。長完全列の Euler 評価と、短完全列のホモロジーの長さの両方向の上界を与える。

## 方針

冪ねじれ性と長さの有限性を確かめた加群を実際のアーベル部分圏に入れ、CategoryTheory の共通の長完全列の定理（`CategoryTheory/Euler`）を適用する。値は ℝ≥0∞ のまま扱う。

## 規約

PerfectComplex の Euler 評価（NormalizedEuler）より下の層に置く（refactor-plan §5.2 の 1）。有限性は有限生成性ではなく、与えた長さの有限性である。

## 使われ方

PerfectComplex の正規化 Euler 評価、LengthAlgebra の全体、Paper の長さ代数。
-/

@[expose] public noncomputable section

universe u

section NormalizedLengthPart

open scoped ENNReal

namespace SerrePositivity

/-- 環 `C` 上の正規化長さ：`C` 加群に `ℝ≥0∞` の値を対応させる関数で、零加群で `0`、同型で不変、
`J` の冪で消える加群の短完全列で加法的なもの。論文の `λ`（Lemma 2.3）を公理化したもので、
`J = m_D C` にとる。`J = ⊥` なら通常の長さ（`ordinary`）。 -/
structure NormalizedLength (C : Type u) [CommRing C] (J : Ideal C) where
  /-- 加群 `M` の長さ `λ(M) ∈ ℝ≥0∞`。すべての `C` 加群に対して定義されるが、加法性は `J` 冪ねじれ
  加群の上でしか要求しない。 -/
  len : (M : Type u) → [AddCommGroup M] → [Module C M] → ℝ≥0∞
  /-- 零加群の長さは `0`。 -/
  len_eq_zero_of_subsingleton : ∀ (M : Type u) [AddCommGroup M] [Module C M] [Subsingleton M],
    len M = 0
  /-- 線形同型な加群は同じ長さをもつ。 -/
  len_congr : ∀ (M N : Type u) [AddCommGroup M] [Module C M] [AddCommGroup N] [Module C N],
    (M ≃ₗ[C] N) → len M = len N
  /-- 短完全列 `0 → M₁ →f M₂ →g M₃ → 0` で、中央の `M₂` が `J` のある冪で消えるなら
  `λ(M₂) = λ(M₁) + λ(M₃)`。両端も `M₂` の部分加群・商なので同じ冪で消える。 -/
  len_add_of_exact : ∀ (M₁ M₂ M₃ : Type u) [AddCommGroup M₁] [Module C M₁]
    [AddCommGroup M₂] [Module C M₂] [AddCommGroup M₃] [Module C M₃]
    (f : M₁ →ₗ[C] M₂) (g : M₂ →ₗ[C] M₃),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
    (∃ n : ℕ, Module.IsTorsionBySet C M₂ (J ^ n : Ideal C)) →
    len M₂ = len M₁ + len M₃

namespace NormalizedLength

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)
variable {M N P : Type u} [AddCommGroup M] [Module C M] [AddCommGroup N] [Module C N]
  [AddCommGroup P] [Module C P]

/-- `J` 冪ねじれ加群 `M` と部分加群 `N` について `λ(M) = λ(N) + λ(M/N)`（短完全列
`0 → N → M → M/N → 0` での加法性）。 -/
lemma len_eq_add_quotient (hM : IsPowTorsion J M) (N : Submodule C M) :
    lam.len M = lam.len N + lam.len (M ⧸ N) :=
  lam.len_add_of_exact N M (M ⧸ N) N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N) hM

/-- 部分加群の長さはもとの加群の長さ以下：`λ(N) ≤ λ(N) + λ(M/N) = λ(M)`（値が非負だから）。 -/
lemma len_submodule_le (hM : IsPowTorsion J M) (N : Submodule C M) : lam.len N ≤ lam.len M := by
  rw [lam.len_eq_add_quotient hM N]
  exact le_self_add

/-- 商加群の長さはもとの加群の長さ以下。 -/
lemma len_quotient_le (hM : IsPowTorsion J M) (N : Submodule C M) :
    lam.len (M ⧸ N) ≤ lam.len M := by
  rw [lam.len_eq_add_quotient hM N]
  exact le_add_self

/-- `J` 冪ねじれ加群 `N` への単射 `f : M → N` があれば `λ(M) ≤ λ(N)`（`M ≅ im f ⊆ N`）。 -/
lemma len_le_of_injective (f : M →ₗ[C] N) (hf : Function.Injective f) (hN : IsPowTorsion J N) :
    lam.len M ≤ lam.len N := by
  rw [lam.len_congr M (LinearMap.range f) (LinearEquiv.ofInjective f hf)]
  exact lam.len_submodule_le hN _

/-- `J` 冪ねじれ加群 `M` からの全射 `f : M → N` があれば `λ(N) ≤ λ(M)`（`N ≅ M / ker f`）。 -/
lemma len_le_of_surjective (f : M →ₗ[C] N) (hf : Function.Surjective f) (hM : IsPowTorsion J M) :
    lam.len N ≤ lam.len M := by
  rw [← lam.len_congr _ _ (LinearMap.quotKerEquivOfSurjective f hf)]
  exact lam.len_quotient_le hM _

/-- `J` 冪ねじれ加群 `M` からの線形写像 `f` について `λ(M) = λ(ker f) + λ(im f)`
（`M / ker f ≅ im f`）。長完全列を像の長さに分解するとき（`NormalizedEuler.lean`）の基本式。 -/
lemma len_eq_add_ker_range (f : M →ₗ[C] N) (hM : IsPowTorsion J M) :
    lam.len M = lam.len (LinearMap.ker f) + lam.len (LinearMap.range f) := by
  rw [lam.len_eq_add_quotient hM (LinearMap.ker f)]
  congr 1
  exact lam.len_congr _ _ (LinearMap.quotKerEquivRange f)

/-- 正規化長さが有限な加群の自己準同型では、核と余核の長さが等しい。
像の長さを加法性の二つの等式から消去する。有限性はこの消去に必要である。 -/
lemma len_ker_eq_len_coker (f : M →ₗ[C] M) (hM : IsPowTorsion J M)
    (hfinite : lam.len M ≠ ⊤) :
    lam.len (LinearMap.ker f) = lam.len (M ⧸ LinearMap.range f) := by
  have hr : lam.len (LinearMap.range f) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (lam.len_submodule_le hM _)
  apply (ENNReal.add_left_inj hr).mp
  rw [← lam.len_eq_add_ker_range f hM, add_comm, ← lam.len_eq_add_quotient hM]

/-- 写像 `f` の核を自己準同型 `g` が消すなら、その長さは `g` の余核の長さ以下。
定理2.5では `g` を共通分母による乗法に適用する。 -/
lemma len_ker_le_len_coker_of_ker_le (f : M →ₗ[C] N) (g : M →ₗ[C] M)
    (hM : IsPowTorsion J M) (hfinite : lam.len M ≠ ⊤)
    (hker : LinearMap.ker f ≤ LinearMap.ker g) :
    lam.len (LinearMap.ker f) ≤ lam.len (M ⧸ LinearMap.range g) := by
  rw [← lam.len_ker_eq_len_coker g hM hfinite]
  exact lam.len_le_of_injective (Submodule.inclusion hker)
    (Submodule.inclusion_injective hker) (hM.submodule _)

/-- `J` 冪ねじれ加群 `M` からの線形写像の像の長さは `λ(M)` 以下。 -/
lemma len_range_le (f : M →ₗ[C] N) (hM : IsPowTorsion J M) :
    lam.len (LinearMap.range f) ≤ lam.len M :=
  lam.len_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict hM

/-- `λ(M) = 0` なら `M` からの線形写像の像も長さ `0`。 -/
lemma len_range_eq_zero (f : M →ₗ[C] N) (hM : IsPowTorsion J M) (h : lam.len M = 0) :
    lam.len (LinearMap.range f) = 0 :=
  le_antisymm (h ▸ lam.len_range_le f hM) zero_le

/-- 完全列 `M →f N →g P`（`M`、`N`、`P` は `J` 冪ねじれ）で `λ(N) ≤ λ(M) + λ(P)`：
`λ(N) = λ(ker g) + λ(im g) = λ(im f) + λ(im g) ≤ λ(M) + λ(P)`。Lemma 3.4 で長完全列から
`Tor` の長さの評価を出すときに使う。 -/
lemma len_le_add_of_exact (f : M →ₗ[C] N) (g : N →ₗ[C] P) (h : Function.Exact f g)
    (hM : IsPowTorsion J M) (hN : IsPowTorsion J N) (hP : IsPowTorsion J P) :
    lam.len N ≤ lam.len M + lam.len P := by
  rw [lam.len_eq_add_ker_range g hN, LinearMap.exact_iff.mp h]
  exact add_le_add (lam.len_range_le f hM) (lam.len_submodule_le hP _)

/-- 完全列 `M → N → P` で `λ(M) = λ(P) = 0` なら `λ(N) = 0`（`len_le_add_of_exact`）。 -/
lemma len_eq_zero_of_exact (f : M →ₗ[C] N) (g : N →ₗ[C] P) (h : Function.Exact f g)
    (hM : IsPowTorsion J M) (hN : IsPowTorsion J N) (hP : IsPowTorsion J P)
    (h1 : lam.len M = 0) (h3 : lam.len P = 0) : lam.len N = 0 := by
  have := lam.len_le_add_of_exact f g h hM hN hP
  rw [h1, h3, add_zero] at this
  exact le_antisymm this zero_le

/-- 完全列 `M → N → P` で `λ(M)`、`λ(P)` が有限なら `λ(N)` も有限（`len_le_add_of_exact`）。 -/
lemma len_ne_top_of_exact (f : M →ₗ[C] N) (g : N →ₗ[C] P) (h : Function.Exact f g)
    (hM : IsPowTorsion J M) (hN : IsPowTorsion J N) (hP : IsPowTorsion J P)
    (h1 : lam.len M ≠ ⊤) (h3 : lam.len P ≠ ⊤) : lam.len N ≠ ⊤ :=
  ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨h1, h3⟩) (lam.len_le_add_of_exact f g h hM hN hP)

/-- 完全列 `M →f N →g P → 0` で `λ(ker f) = 0` なら `λ(N) = λ(M) + λ(P)`：
`λ(N) = λ(im f) + λ(P)` かつ `λ(M) = λ(ker f) + λ(im f) = λ(im f)`。`f` が単射でなくても、核の
長さが `0` なら加法性が成り立つ、という形で Lemma 3.4 の組成列の帰納法に使う。 -/
lemma len_eq_add_of_exact_of_surjective (f : M →ₗ[C] N) (g : N →ₗ[C] P)
    (h : Function.Exact f g) (hg : Function.Surjective g)
    (hM : IsPowTorsion J M) (hN : IsPowTorsion J N)
    (hker : lam.len (LinearMap.ker f) = 0) : lam.len N = lam.len M + lam.len P := by
  rw [lam.len_eq_add_ker_range g hN, LinearMap.exact_iff.mp h, LinearMap.range_eq_top.mpr hg,
    lam.len_eq_add_ker_range f hM, hker, zero_add]
  congr 1
  exact lam.len_congr _ _ Submodule.topEquiv

/-- 加法性の定義域のイデアルの取り替え：`J'` 冪ねじれ加群がつねに `J` 冪ねじれなら、`J` の正規化
長さは `J'` の正規化長さでもある（加法性を要求する加群のクラスが狭まるだけ）。値は変わらない。 -/
def restrict (lam : NormalizedLength C J) (J' : Ideal C)
    (h : ∀ (M : Type u) [AddCommGroup M] [Module C M], IsPowTorsion J' M → IsPowTorsion J M) :
    NormalizedLength C J' where
  len := lam.len
  len_eq_zero_of_subsingleton := lam.len_eq_zero_of_subsingleton
  len_congr := lam.len_congr
  len_add_of_exact := by
    intro M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg hM₂
    exact lam.len_add_of_exact M₁ M₂ M₃ f g hf hg hfg (h M₂ hM₂)

/-- `restrict` は値を変えない。 -/
@[simp] lemma restrict_len (lam : NormalizedLength C J) (J' : Ideal C) (h) (M : Type u)
    [AddCommGroup M] [Module C M] : (lam.restrict J' h).len M = lam.len M := rfl

/-- 通常の長さ `Module.length` は `J = ⊥` の正規化長さである（`ℕ∞` を `ℝ≥0∞` に埋め込む）。
短完全列での加法性は Mathlib の `Module.length_eq_add_of_exact`。`IsPowTorsion ⊥ M` はどの `M` でも
成り立つ（`IsPowTorsion.bot`）ので、正規化長さについての Euler 評価の定理はすべて通常の長さに
特殊化できる（`NormalizedEuler.lean`、`OrdinaryEuler.lean`）。 -/
noncomputable def ordinary (T : Type u) [CommRing T] : NormalizedLength T ⊥ where
  len := by
    intro M _ _
    exact (Module.length T M : ℝ≥0∞)
  len_eq_zero_of_subsingleton := by
    intro M _ _ _
    simp [Module.length_eq_zero]
  len_congr := by
    intro M N _ _ _ _ e
    rw [e.length_eq]
  len_add_of_exact := by
    intro M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg _
    rw [Module.length_eq_add_of_exact f g hf hg hfg, ENat.toENNReal_add]

/-- `(ordinary T).len M = Module.length T M`（`ℝ≥0∞` の値として）。 -/
@[simp] lemma ordinary_len (T : Type u) [CommRing T] (M : Type u) [AddCommGroup M]
    [Module T M] : (ordinary T).len M = (Module.length T M : ℝ≥0∞) := rfl

/-- 論文の `λ` は `m_D C` 冪ねじれ加群の上で加法的だが、Lemma 3.4・3.5 では `m_A C` 冪ねじれ加群を
扱う。`D` が局所環 `A` 上有限なら `m_D^N ⊆ m_A D`（`maximalIdeal_pow_le_map_of_finite`）なので、
`m_A C` 冪ねじれ加群は `m_D C` 冪ねじれ（`IsPowTorsion.of_pow_le`）であり、`restrict` で定義域を
`m_A C` に取り替えられる。値は変わらない。 -/
def restrictToBase (A D : Type u) [CommRing A] [IsLocalRing A]
    [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    {C : Type u} [CommRing C] [Algebra A C] [Algebra D C] [IsScalarTower A D C]
    (lam : NormalizedLength C ((IsLocalRing.maximalIdeal D).map (algebraMap D C))) :
    NormalizedLength C ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) := by
  exact lam.restrict _ (fun M _ _ hM ↦ IsPowTorsion.of_pow_le
    (maximalIdeal_pow_le_map_of_finite (R := A) D) M hM)

end NormalizedLength

end SerrePositivity

end NormalizedLengthPart

section SerreQuotientPart

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject ENNReal

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 冪ねじれ加群の短完全列における長さの加法性。 -/
lemma module_length_add {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (h₂ : IsPowTorsion J S.X₂) :
    lam.len S.X₂ = lam.len S.X₁ + lam.len S.X₃ :=
  lam.len_add_of_exact _ _ _ S.f.hom S.g.hom hS.moduleCat_injective_f
    hS.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) h₂

/-- 有限の長さをもつ冪ねじれ加群。 -/
def finiteLengthTorsion : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ IsPowTorsion J M ∧ lam.len M ≠ ⊤

instance : (finiteLengthTorsion lam).ContainsZero where
  exists_zero := by
    have : Subsingleton (0 : ModuleCat.{u} R) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
    refine ⟨0, isZero_zero _, IsPowTorsion.of_subsingleton, ?_⟩
    rw [lam.len_eq_zero_of_subsingleton]
    exact ENNReal.zero_ne_top

instance : (finiteLengthTorsion lam).IsClosedUnderSubobjects where
  prop_of_mono f _ hN :=
    ⟨IsPowTorsion.of_injective f.hom ((ModuleCat.mono_iff_injective _).mp inferInstance) hN.1,
      ne_top_of_le_ne_top hN.2
        (lam.len_le_of_injective f.hom ((ModuleCat.mono_iff_injective _).mp inferInstance) hN.1)⟩

instance : (finiteLengthTorsion lam).IsClosedUnderQuotients where
  prop_of_epi f _ hM :=
    ⟨IsPowTorsion.of_surjective f.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance) hM.1,
      ne_top_of_le_ne_top hM.2
        (lam.len_le_of_surjective f.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance) hM.1)⟩

instance : (finiteLengthTorsion lam).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have ht := (powTorsionModule J).prop_X₂_of_shortExact hS h₁.1 h₃.1
    refine ⟨ht, ?_⟩
    rw [module_length_add lam hS ht]
    exact ENNReal.add_ne_top.mpr ⟨h₁.2, h₃.2⟩

instance : (finiteLengthTorsion lam).IsSerreClass where

/-- 有限な長さの冪ねじれ加群のアーベル圏。 -/
abbrev FiniteLengthTorsion := (finiteLengthTorsion lam).FullSubcategory

/-- 有限性を確認した対象の実数値の長さ。 -/
noncomputable def finiteLength (M : FiniteLengthTorsion lam) : ℝ := (lam.len M.obj).toReal

lemma finiteLength_nonneg (M : FiniteLengthTorsion lam) : 0 ≤ finiteLength lam M :=
  ENNReal.toReal_nonneg

lemma finiteLength_iso {M N : FiniteLengthTorsion lam} (e : M ≅ N) :
    finiteLength lam M = finiteLength lam N := by
  have h : lam.len M.obj = lam.len N.obj :=
    lam.len_congr _ _ (((finiteLengthTorsion lam).ι).mapIso e).toLinearEquiv
  exact congrArg ENNReal.toReal h

lemma finiteLength_of_isZero (M : FiniteLengthTorsion lam) (hM : IsZero M) :
    finiteLength lam M = 0 := by
  have : Subsingleton M.obj := ModuleCat.isZero_iff_subsingleton.mp
    ((finiteLengthTorsion lam).ι.map_isZero hM)
  simp [finiteLength, lam.len_eq_zero_of_subsingleton]

lemma finiteLength_add {S : ShortComplex (FiniteLengthTorsion lam)} (hS : S.ShortExact) :
    finiteLength lam S.X₂ = finiteLength lam S.X₁ + finiteLength lam S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have h := module_length_add lam (hS.map (finiteLengthTorsion lam).ι) S.X₂.property.1
  change lam.len S.X₂.obj = lam.len S.X₁.obj + lam.len S.X₃.obj at h
  dsimp only [finiteLength]
  rw [h, ENNReal.toReal_add S.X₁.property.2 S.X₃.property.2]

instance : (zeroAdditiveLength (finiteLength lam)).IsSerreClass :=
  zeroAdditiveLength_isSerreClass (finiteLength lam) (finiteLength_add lam)
    (finiteLength_nonneg lam) (finiteLength_of_isZero lam _ (isZero_zero _))

/-- 有限な長さの冪ねじれ加群を零長さで割ったアーベル圏。 -/
abbrev FiniteLengthQuotient := (zeroAdditiveLength (finiteLength lam)).isoModSerre.Localization

/-- 有限な長さの商への完全関手。 -/
noncomputable abbrev finiteLengthQuotientFunctor :
    FiniteLengthTorsion lam ⥤ FiniteLengthQuotient lam :=
  (zeroAdditiveLength (finiteLength lam)).isoModSerre.Q

noncomputable instance : PreservesFiniteLimits (finiteLengthQuotientFunctor lam) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits
    (finiteLengthQuotientFunctor lam) (zeroAdditiveLength (finiteLength lam))

noncomputable instance : PreservesFiniteColimits (finiteLengthQuotientFunctor lam) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits
    (finiteLengthQuotientFunctor lam) (zeroAdditiveLength (finiteLength lam))

/-- 有限商の実数値の長さ。 -/
noncomputable def quotientLength : FiniteLengthQuotient lam → ℝ :=
  serreQuotientLength (zeroAdditiveLength (finiteLength lam)) (finiteLength lam)

@[simp] lemma quotientLength_obj (M : FiniteLengthTorsion lam) :
    quotientLength lam ((finiteLengthQuotientFunctor lam).obj M) = (lam.len M.obj).toReal := rfl

lemma quotientLength_iso {X Y : FiniteLengthQuotient lam} (e : X ≅ Y) :
    quotientLength lam X = quotientLength lam Y :=
  serreQuotientLength_iso (zeroAdditiveLength (finiteLength lam)) (finiteLength lam)
    (finiteLength_iso lam) (finiteLength_add lam) (fun _ h ↦ h) e

lemma quotientLength_add {S : ShortComplex (FiniteLengthQuotient lam)} (hS : S.ShortExact) :
    quotientLength lam S.X₂ = quotientLength lam S.X₁ + quotientLength lam S.X₃ :=
  serreQuotientLength_add (zeroAdditiveLength (finiteLength lam)) (finiteLength lam)
    (finiteLength_iso lam) (finiteLength_add lam) (fun _ h ↦ h) hS

lemma quotientLength_eq_zero_iff (X : FiniteLengthQuotient lam) :
    quotientLength lam X = 0 ↔ IsZero X :=
  serreQuotientLength_eq_zero_iff (zeroAdditiveLength (finiteLength lam)) (finiteLength lam)
    (fun _ ↦ Iff.rfl) X

/-- 全ての冪ねじれ加群に定義された、無限値を許す長さ。 -/
def torsionLength (M : PowTorsionModule J) : ℝ≥0∞ := lam.len M.obj

lemma torsionLength_iso {M N : PowTorsionModule J} (e : M ≅ N) :
    torsionLength lam M = torsionLength lam N :=
  lam.len_congr _ _ ((powTorsionModule J).ι.mapIso e).toLinearEquiv

lemma torsionLength_of_isZero (M : PowTorsionModule J) (hM : IsZero M) :
    torsionLength lam M = 0 := by
  have : Subsingleton M.obj := ModuleCat.isZero_iff_subsingleton.mp
    ((powTorsionModule J).ι.map_isZero hM)
  exact lam.len_eq_zero_of_subsingleton _

lemma torsionLength_add {S : ShortComplex (PowTorsionModule J)} (hS : S.ShortExact) :
    torsionLength lam S.X₂ = torsionLength lam S.X₁ + torsionLength lam S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  exact module_length_add lam (hS.map (powTorsionModule J).ι) S.X₂.property

instance : (zeroAdditiveLength (torsionLength lam)).IsSerreClass :=
  zeroAdditiveLength_isSerreClass (torsionLength lam) (torsionLength_add lam)
    (fun _ ↦ bot_le) (torsionLength_of_isZero lam _ (isZero_zero _))

/-- 無限長も含む冪ねじれ加群を、零長さで割った商。 -/
abbrev LengthQuotient := (zeroAdditiveLength (torsionLength lam)).isoModSerre.Localization

noncomputable abbrev lengthQuotientFunctor : PowTorsionModule J ⥤ LengthQuotient lam :=
  (zeroAdditiveLength (torsionLength lam)).isoModSerre.Q

noncomputable instance : PreservesFiniteLimits (lengthQuotientFunctor lam) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits
    (lengthQuotientFunctor lam) (zeroAdditiveLength (torsionLength lam))

noncomputable instance : PreservesFiniteColimits (lengthQuotientFunctor lam) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits
    (lengthQuotientFunctor lam) (zeroAdditiveLength (torsionLength lam))

/-- 大きな商に降下した非負拡大実数値の長さ。 -/
noncomputable def extendedQuotientLength : LengthQuotient lam → ℝ≥0∞ :=
  serreQuotientLength (zeroAdditiveLength (torsionLength lam)) (torsionLength lam)

@[simp] lemma extendedQuotientLength_obj (M : PowTorsionModule J) :
    extendedQuotientLength lam ((lengthQuotientFunctor lam).obj M) = lam.len M.obj := rfl

lemma extendedQuotientLength_eq_zero_iff (X : LengthQuotient lam) :
    extendedQuotientLength lam X = 0 ↔ IsZero X :=
  serreQuotientLength_eq_zero_iff (zeroAdditiveLength (torsionLength lam)) (torsionLength lam)
    (fun _ ↦ Iff.rfl) X

end SerrePositivity.LengthAlgebra

end SerreQuotientPart

section ExactSequenceEulerPart

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

set_option backward.isDefEq.respectTransparency false in
/-- 元の加群の長さによる Euler 加法性は、有限長さ部分圏での共通定理の適用である。 -/
theorem normalizedLength_euler_exact_sequence
    (X₁ X₂ X₃ : ℤ → ModuleCat.{u} R)
    (α : ∀ i, X₁ i ⟶ X₂ i) (β : ∀ i, X₂ i ⟶ X₃ i)
    (δ : ∀ i, X₃ i ⟶ X₁ (i + 1))
    {w₂ : ∀ i, α i ≫ β i = 0} {w₃ : ∀ i, β i ≫ δ i = 0}
    {w₁ : ∀ i, δ i ≫ α (i + 1) = 0}
    (h₂ : ∀ i, (ShortComplex.mk (α i) (β i) (w₂ i)).Exact)
    (h₃ : ∀ i, (ShortComplex.mk (β i) (δ i) (w₃ i)).Exact)
    (h₁ : ∀ i, (ShortComplex.mk (δ i) (α (i + 1)) (w₁ i)).Exact)
    (t₁ : ∀ i, IsPowTorsion J (X₁ i)) (t₂ : ∀ i, IsPowTorsion J (X₂ i))
    (t₃ : ∀ i, IsPowTorsion J (X₃ i))
    (l₁ : ∀ i, lam.len (X₁ i) ≠ ⊤) (l₂ : ∀ i, lam.len (X₂ i) ≠ ⊤)
    (l₃ : ∀ i, lam.len (X₃ i) ≠ ⊤)
    (hb₂ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₂ i))
    (hb₃ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₃ i)) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (X₂ i)).toReal) =
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (X₁ i)).toReal) +
        ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (X₃ i)).toReal := by
  let Y₁ : ℤ → FiniteLengthTorsion lam := fun i ↦ ⟨X₁ i, t₁ i, l₁ i⟩
  let Y₂ : ℤ → FiniteLengthTorsion lam := fun i ↦ ⟨X₂ i, t₂ i, l₂ i⟩
  let Y₃ : ℤ → FiniteLengthTorsion lam := fun i ↦ ⟨X₃ i, t₃ i, l₃ i⟩
  let a : ∀ i, Y₁ i ⟶ Y₂ i := fun i ↦ ObjectProperty.homMk (α i)
  let b : ∀ i, Y₂ i ⟶ Y₃ i := fun i ↦ ObjectProperty.homMk (β i)
  let d : ∀ i, Y₃ i ⟶ Y₁ (i + 1) := fun i ↦ ObjectProperty.homMk (δ i)
  have v₂ (i : ℤ) : a i ≫ b i = 0 := ObjectProperty.hom_ext _ (w₂ i)
  have v₃ (i : ℤ) : b i ≫ d i = 0 := ObjectProperty.hom_ext _ (w₃ i)
  have v₁ (i : ℤ) : d i ≫ a (i + 1) = 0 := ObjectProperty.hom_ext _ (w₁ i)
  simp only [← zsmul_eq_mul]
  apply additiveLength_euler_exact_sequence (finiteLength lam) (finiteLength_iso lam)
    (finiteLength_add lam) (finiteLength_of_isZero lam) Y₁ Y₂ Y₃ a b d
    (w₂ := v₂) (w₃ := v₃) (w₁ := v₁)
  · intro i
    exact (ShortComplex.exact_map_iff_of_faithful _ (finiteLengthTorsion lam).ι).mp (h₂ i)
  · intro i
    exact (ShortComplex.exact_map_iff_of_faithful _ (finiteLengthTorsion lam).ι).mp (h₃ i)
  · intro i
    exact (ShortComplex.exact_map_iff_of_faithful _ (finiteLengthTorsion lam).ι).mp (h₁ i)
  · obtain ⟨a, b, hab⟩ := hb₂
    exact ⟨a, b, fun i hi ↦ IsZero.of_full_of_faithful_of_isZero
      (finiteLengthTorsion lam).ι _ (hab i hi)⟩
  · obtain ⟨a, b, hab⟩ := hb₃
    exact ⟨a, b, fun i hi ↦ IsZero.of_full_of_faithful_of_isZero
      (finiteLengthTorsion lam).ι _ (hab i hi)⟩

end SerrePositivity.LengthAlgebra

end ExactSequenceEulerPart

section HomologyExactBoundsPart

namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 短完全列の中央のホモロジーの長さは両端の和以下。
ホモロジーの長完全列と、冪ねじれ加群上の長さの劣加法性を使う。 -/
lemma lambdaHomology_shortExact_le
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) (q : ℤ)
    (t₁ : IsPowTorsion J (S.X₁.homology q))
    (t₂ : IsPowTorsion J (S.X₂.homology q))
    (t₃ : IsPowTorsion J (S.X₃.homology q)) :
    lam.len (S.X₂.homology q) ≤ lam.len (S.X₁.homology q) + lam.len (S.X₃.homology q) :=
  lam.len_le_add_of_exact (HomologicalComplex.homologyMap S.f q).hom
    (HomologicalComplex.homologyMap S.g q).hom
    (LinearMap.exact_iff.mpr (hS.homology_exact₂ q).moduleCat_range_eq_ker.symm) t₁ t₂ t₃

/-- 左のホモロジーの長さは、余核の一つ前の次数と中央の同次数の和以下。 -/
theorem lambdaHomology_shortExact_left_le
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) (q : ℤ)
    (t₃prev : IsPowTorsion J (S.X₃.homology (q - 1)))
    (t₁ : IsPowTorsion J (S.X₁.homology q))
    (t₂ : IsPowTorsion J (S.X₂.homology q)) :
    lam.len (S.X₁.homology q) ≤ lam.len (S.X₃.homology (q - 1)) +
      lam.len (S.X₂.homology q) := by
  have hrel : (ComplexShape.up ℤ).Rel (q - 1) q := by simp
  exact lam.len_le_add_of_exact (hS.δ (q - 1) q hrel).hom
    (HomologicalComplex.homologyMap S.f q).hom
    (LinearMap.exact_iff.mpr (hS.homology_exact₁ (q - 1) q hrel).moduleCat_range_eq_ker.symm)
    t₃prev t₁ t₂

/-- 誤差複体の隣接する二次数の長さが零なら、比較するホモロジーの長さは一致。
比較する長さが有限であるという追加仮定は不要。 -/
theorem lambdaHomology_shortExact_eq_of_error_zero
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) (q : ℤ)
    (t₁ : IsPowTorsion J (S.X₁.homology q))
    (t₂ : IsPowTorsion J (S.X₂.homology q))
    (t₃ : IsPowTorsion J (S.X₃.homology q))
    (t₃prev : IsPowTorsion J (S.X₃.homology (q - 1)))
    (hprev : lam.len (S.X₃.homology (q - 1)) = 0)
    (hcurrent : lam.len (S.X₃.homology q) = 0) :
    lam.len (S.X₁.homology q) = lam.len (S.X₂.homology q) := by
  apply le_antisymm
  · simpa only [hprev, zero_add] using
      lambdaHomology_shortExact_left_le lam S hS q t₃prev t₁ t₂
  · simpa only [hcurrent, add_zero] using
      lambdaHomology_shortExact_le lam S hS q t₁ t₂ t₃

/-- 誤差側のホモロジーの長さは、中央の同次数と左の次の次数の和以下。 -/
theorem lambdaHomology_shortExact_right_le
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) (q : ℤ)
    (t₂ : IsPowTorsion J (S.X₂.homology q))
    (t₃ : IsPowTorsion J (S.X₃.homology q))
    (t₁next : IsPowTorsion J (S.X₁.homology (q + 1))) :
    lam.len (S.X₃.homology q) ≤ lam.len (S.X₂.homology q) +
      lam.len (S.X₁.homology (q + 1)) := by
  have hrel : (ComplexShape.up ℤ).Rel q (q + 1) := by simp
  exact lam.len_le_add_of_exact (HomologicalComplex.homologyMap S.g q).hom
    (hS.δ q (q + 1) hrel).hom
    (LinearMap.exact_iff.mpr (hS.homology_exact₃ q (q + 1) hrel).moduleCat_range_eq_ker.symm)
    t₂ t₃ t₁next

/-- 中央の同次数と左の次の次数の長さが有限なら、誤差側の長さも有限。 -/
theorem lambdaHomology_shortExact_right_ne_top
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) (q : ℤ)
    (t₂ : IsPowTorsion J (S.X₂.homology q))
    (t₃ : IsPowTorsion J (S.X₃.homology q))
    (t₁next : IsPowTorsion J (S.X₁.homology (q + 1)))
    (h₂ : lam.len (S.X₂.homology q) ≠ ⊤)
    (h₁next : lam.len (S.X₁.homology (q + 1)) ≠ ⊤) :
    lam.len (S.X₃.homology q) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨h₂, h₁next⟩)
    (lambdaHomology_shortExact_right_le lam S hS q t₂ t₃ t₁next)

end SerrePositivity

end HomologyExactBoundsPart

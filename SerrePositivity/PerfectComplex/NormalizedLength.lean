module

public import SerrePositivity.CommutativeAlgebra.LocalAlgebra
public import SerrePositivity.CommutativeAlgebra.PowTorsion
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.RingTheory.Length

/-!
# 正規化長さ

## 概要

論文 Lemma 2.3 と §3.4 冒頭の「正規化長さ」を抽象化した構造 `NormalizedLength C J`：環 `C` の加群に
`ℝ≥0∞` の値を対応させる関数 `len` で、零加群で `0`、同型で不変、イデアル `J` の冪で消える加群の
短完全列で加法的なもの。論文では、正則局所環 `A` 上有限な局所環 `D` とその上の代数 `C` について、
`m_D C` の冪で消える `C` 加群に対して正規化された長さ `λ` を定め（Lemma 2.3）、`Tor` の Euler 評価
`Σ (-1)^i λ(Tor_i)` を考える。このファイルはそこで使われる性質だけを公理化する。

## 方針

論文の正規化長さの具体的な構成や、上限による評価 (2.3) は含めない。Lemma 3.4、3.5a、
Corollary 2.6、§5 の議論で使うのは、同型不変性と短完全列での加法性（と、そこから出る単調性）
だけだからである。具体的な正規化長さの存在は `Inputs/LengthAlgebra.lean` の `Inputs.exists_lengthAlgebra` で未証明定理として述べる。

値を `ℝ≥0∞` にとるのは、論文 §1.4 の規約（長さは無限でもよい）に合わせるため。加法性の対象を
`J` 冪ねじれ加群に限るのは、論文の `λ` が `m_D C` の冪で消える加群の上でしか加法的でないからである。

## 内容

- 構造 `NormalizedLength` と、加法性・非負性から出る基本補題：部分加群・商・単射・全射に対する
  単調性、`len M = len (ker f) + len (range f)`、完全列 `M → N → P` に対する
  `len N ≤ len M + len P`、両端が `0` なら中央も `0`、両端が有限なら中央も有限。Lemma 3.4 の証明
  （`notes/lemma-3-4.md`）と `NormalizedEuler.lean` で使う。
- 定義域のイデアルの取り替え `restrict` と、`m_D C` から `m_A C` への取り替え `restrictToBase`。
- 通常の長さ `Module.length` は `J = ⊥` の正規化長さ `ordinary`。

正規化長さによる Euler 評価（複体の `lambdaEuler`、`Tor` の `lambdaChi`）は `NormalizedEuler.lean`。
-/

@[expose] public section

universe u

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

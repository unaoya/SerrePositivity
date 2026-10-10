module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import SerrePositivity.CommutativeAlgebra.Koszul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# 正則局所環についての未証明の入力

## 概要

正則局所環の標準的な二つの事実を、`sorry` 付きの定理として置く（`notes/PLAN.md` の層 3a）。

- **A1**（`isWeaklyRegular_of_span_eq_maximalIdeal`）：正則局所環 `A` の正則パラメータ系
  （`m_A` を生成する `dim A` 個の元）は弱正則列である。Koszul 複体 `K(z)` が剰余体の分解であること
  （`CommutativeAlgebra/KoszulResolution.lean`）の前提で、Lemma 3.4・3.5 の正規化長さ側と
  Corollary 2.6 で使う。
- **Koszul Euler 標数 = 階数**（`koszulEulerChar_eq_finrank`）：`A` 上有限な代数 `T` について
  `χ^A(z; T) = rank_A T`。Lemma 3.5b の通常の長さ側（`Paper/Lemma3_5/Ordinary.lean`）で、
  `χ_A(K(z) ⊗_A T) = rank_A T` として使う。

どちらも Mathlib にまだない（A1 は正則局所環の理論、後者は Serre の Koszul ホモロジーと重複度の
定理）。Mathlib との対応と残る接続の検討は `notes/mathlib-review-2026-10-10.md`。これらを使う定理
には `sorryAx` への依存が残る。

有限な局所代数の極大イデアルの冪が基底の極大イデアルの拡大に入る事実は、以前はここに入力として
置いていたが、`CommutativeAlgebra/LocalAlgebra.lean` で証明した
（`maximalIdeal_pow_le_map_of_finite`）。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- **A1**（層 3a、未証明）：正則局所環 `A` で、`z = (z_1, …, z_e)` が `m_A` を生成し `e = dim A` なら、
`z` は弱正則列（各 `z_i` が `A/(z_1, …, z_{i-1})` の非零因子）。正則局所環の正則パラメータ系が
正則列であるという標準的な事実。 -/
theorem isWeaklyRegular_of_span_eq_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {e : ℕ} (z : Fin e → A) (_hz : Ideal.span (Set.range z) = maximalIdeal A)
    (_he : ringKrullDim A = e) : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z) := by
  sorry

/-- **Koszul Euler 標数 = 階数**（層 3a、未証明）：正則局所環 `A` の正則パラメータ系 `z` と `A` 上有限な
代数 `T` について、`K(z; T)` のホモロジーを `A` 上の長さで測った Euler 標数
`χ^A(z; T) = Σ (-1)^i ℓ_A(H_i(z; T))`（`CommutativeAlgebra/Koszul.lean` の `koszulEulerChar`）は
`rank_A T = dim_{Frac A}(T ⊗ Frac A)` に等しい。Serre の定理 `χ(z; M) = e(z; M)` と、重複度が
階数に比例すること `e(z; M) = rank_A M · e(z; A)`、`e(z; A) = 1`（正則パラメータ系）による。論文
(3.14) では `T` の有限自由 `A` 分解の階数の交代和として計算している。 -/
theorem koszulEulerChar_eq_finrank (A T : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T]
    [Algebra A T] [Module.Finite A T] {e : ℕ} (z : Fin e → A)
    (_hz : Ideal.span (Set.range z) = maximalIdeal A) (_he : ringKrullDim A = e) :
    koszulEulerChar A T z = Module.finrank A T := by
  sorry

end SerrePositivity

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import SerrePositivity.CommutativeAlgebra.Koszul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# 正則局所環に関する未証明の一般的な入力

二つの標準的な主張を `sorry` 付きの定理として置く。
極大イデアルを環の次元個の元で生成した列が弱正則列になることと、
その列の Koszul Euler 標数が有限代数の階数に一致することである。
このファイルを通じて使う定理には、これらの未証明結果への依存が残る。

有限な局所代数の極大イデアルの冪が基底の極大イデアルの拡大に入る事実は、
`CommutativeAlgebra/LocalAlgebra.lean` ですでに証明されている。
Mathlib との対応と残る接続の検討は `notes/mathlib-review-2026-10-10.md` を参照する。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- **A1**：正則局所環の正則パラメータ系は弱正則列（層 3a、未証明）。 -/
theorem isWeaklyRegular_of_span_eq_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {e : ℕ} (z : Fin e → A) (_hz : Ideal.span (Set.range z) = maximalIdeal A)
    (_he : ringKrullDim A = e) : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z) := by
  sorry

/-- **Koszul Euler 標数 = 生成ランク**（層 3a、未証明）。正則局所環 `A` の正則パラメータ系 `z` と
`A` 上有限な代数 `T` について `χ^A(z; T) = rank_A T`（`koszulEulerChar` は
`CommutativeAlgebra/Koszul.lean`）。
Serre の定理 `χ(z; M) = e(z; M)` と `e(z; M) = rank_A M · e(z; A)`、`e(z; A) = 1` による。
論文 (3.14) では `T` の有限自由 `A` 分解の交代ランクとして計算している。 -/
theorem koszulEulerChar_eq_finrank (A T : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T]
    [Algebra A T] [Module.Finite A T] {e : ℕ} (z : Fin e → A)
    (_hz : Ideal.span (Set.range z) = maximalIdeal A) (_he : ringKrullDim A = e) :
    koszulEulerChar A T z = Module.finrank A T := by
  sorry

end SerrePositivity

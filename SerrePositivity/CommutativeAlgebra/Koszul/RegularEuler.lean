module

public import SerrePositivity.HomologicalAlgebra.Resolution.FiniteFree
public import SerrePositivity.IntersectionMultiplicity.ResolutionEvaluation
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import SerrePositivity.CommutativeAlgebra.Koszul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # 正則局所環の Koszul Euler 標数

## 概要

正則局所環 `A` の正則パラメータ系 `z` と有限 `A` 代数 `T` について `χ^A(z; T) = rank_A T`
（`koszulEulerChar_eq_finrank`）。

## 方針

Koszul 分解（`z` は正則列）で `χ^A(T, A/(z))` に移し、`T` の有限自由分解の Euler–Poincaré 公式と、
`A/(z)` が剰余体で長さ 1 であることを使う。

## 規約

正則局所環の基本（整域性・正則系）は `RegularLocalRing/Basic`。この定理の置き場所は B 群の整理で
`Koszul/RegularEuler` へ移す予定。

## 使われ方

論文 Lemma 3.5、Theorem 4.7、§5 の長さ代数の正値性、重複度の公式。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- **Koszul Euler 標数 = 階数**：正則局所環 `A` の正則パラメータ系 `z` と有限 `A` 代数 `T` に対し、
`χ^A(z; T) = rank_A T`。まず Koszul 分解から `χ^A(T, A/(z))` に移し、`T` の有限自由分解の
Euler–Poincaré 公式と、分解の階数の交代和を使う。`A/(z)` は剰余体なので長さは `1`。
正則パラメータ・整域性・有限自由分解・一般の Euler–Poincaré 公式は全て証明済み。 -/
theorem koszulEulerChar_eq_finrank (A T : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T]
    [Algebra A T] [Module.Finite A T] {e : ℕ} (z : Fin e → A)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (he : ringKrullDim A = e) :
    koszulEulerChar A T z = Module.finrank A T := by
  have hK := isKoszulResolution_of_isWeaklyRegular z
    (isWeaklyRegular_of_span_eq_maximalIdeal A z hz he)
  have := isSimpleModule_quotient_span_of_eq hz
  have hlength : IsFiniteLength A (A ⧸ Ideal.span (Set.range z)) :=
    Module.length_ne_top_iff.mp (by rw [Module.length_eq_one A _]; simp)
  obtain ⟨F, ⟨hF⟩, hb, hfree, hfinite⟩ := regularResolution A T
  rw [koszulEulerChar_eq_chi A T z hK,
    chi_eq_finrank_mul_length_of_resolution A T (A ⧸ Ideal.span (Set.range z))
      hlength F hF hfree hfinite hb,
    Module.length_eq_one A _]
  simp

end SerrePositivity

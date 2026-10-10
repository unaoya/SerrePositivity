module

public import SerrePositivity.Inputs.IntersectionTheory
public import SerrePositivity.IntersectionMultiplicity.ResolutionEvaluation
public import SerrePositivity.Inputs.RegularParameters
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import SerrePositivity.CommutativeAlgebra.Koszul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# 正則局所環への一般定理の適用

正則パラメータの正則性 `isWeaklyRegular_of_span_eq_maximalIdeal` のみを
`Inputs/RegularParameters.lean` で未証明入力として引用する。

- `isDomain_of_isRegularLocalRing`：正則生成列を持つ Noether 局所環の一般論から整域性を導く。
- `koszulEulerChar_eq_finrank`：Koszul 分解と有限自由分解の Euler–Poincaré 公式から
  Koszul Euler 標数が階数と等しいことを導く。

有界有限自由分解の存在 `Inputs.regularResolution` も正則生成列から証明済み。
したがってこのファイルの結論には `sorryAx` が現れるが、正則局所環に関して残る
未証明の入力は正則パラメータの正則性一つである。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- 正則局所環は整域である。極大イデアルの正則生成列を選び、
Noether 局所環に関する一般定理 `isDomain_of_regular_generators` を適用する。
正則パラメータの正則性だけが未証明入力であり、この定理自身に `sorry` はない。 -/
theorem isDomain_of_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsDomain A := by
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators A
  exact isDomain_of_regular_generators rs hreg hgen

/-- **Koszul Euler 標数 = 階数**：正則局所環 `A` の正則パラメータ系 `z` と有限 `A` 代数 `T` に対し、
`χ^A(z; T) = rank_A T`。まず Koszul 分解から `χ^A(T, A/(z))` に移し、`T` の有限自由分解の
Euler–Poincaré 公式と、分解の階数の交代和を使う。`A/(z)` は剰余体なので長さは `1`。
この定理自身に `sorry` はないが、正則パラメータの正則性という
名前付き未証明入力に依存する。整域性と有限自由分解の存在はそこから証明済み。一般の Euler–Poincaré 公式は証明済み。 -/
theorem koszulEulerChar_eq_finrank (A T : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T]
    [Algebra A T] [Module.Finite A T] {e : ℕ} (z : Fin e → A)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (he : ringKrullDim A = e) :
    koszulEulerChar A T z = Module.finrank A T := by
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  have hK := isKoszulResolution_of_isWeaklyRegular z
    (isWeaklyRegular_of_span_eq_maximalIdeal A z hz he)
  have := isSimpleModule_quotient_span_of_eq hz
  have hlength : IsFiniteLength A (A ⧸ Ideal.span (Set.range z)) :=
    Module.length_ne_top_iff.mp (by rw [Module.length_eq_one A _]; simp)
  obtain ⟨F, ⟨hF⟩, hb, hfree, hfinite⟩ := Inputs.regularResolution A T
  rw [koszulEulerChar_eq_chi A T z hK,
    chi_eq_finrank_mul_length_of_resolution A T (A ⧸ Ideal.span (Set.range z))
      hlength F hF hfree hfinite hb,
    Module.length_eq_one A _]
  simp

end SerrePositivity

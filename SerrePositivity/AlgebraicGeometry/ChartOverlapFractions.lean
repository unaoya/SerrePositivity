module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartOverlap

/-!
概要：KST §5、Stacks 080Y のチャートの重なりにおける斉次分数の比較。
方針：重なりでも正則な a の係数像の冪で分母を払い、二つの係数写像の一致を使う。
規約：重なりへの写像自体の単射性は仮定しない。
使われ方：斉次な分子による中心の降下の逆包含。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/--
概要：第一のチャートで正則な a の係数像は重なりでも正則。
方針：比による局所化が非零因子を保つことを使う。
規約：KST §5、Stacks 080Y、比そのものの正則性は要求しない。
使われ方：重なりでの斉次分母の消去。
-/
theorem chartOverlap_left_regular :
    chartOverlapFromLeft I a b (chartBaseMap I a a.1) ∈
      nonZeroDivisors (BlowupOverlapRing I a b) := by
  let := (chartOverlapFromLeft I a b).toAlgebra
  have := chartOverlap_isLocalizationLeft I a b
  exact IsLocalization.nonZeroDivisors_le_comap (S := BlowupOverlapRing I a b)
    (Submonoid.powers (chartRatio I a b)) (chartBaseMap_mem_nonZeroDivisors I a)

/--
概要：第一のチャートの比 b/a は重なり環で単元。
方針：重なりをその比の通常の局所化とした普遍条件を使う。
規約：KST §5、Stacks 080Y、比は元のチャートでは零因子でもよい。
使われ方：重なり上の分数のイデアル所属で比の冪を消去する。
-/
theorem chartOverlap_left_ratio_isUnit :
    IsUnit (chartOverlapFromLeft I a b (chartRatio I a b)) := by
  let := (chartOverlapFromLeft I a b).toAlgebra
  have := chartOverlap_isLocalizationLeft I a b
  exact IsLocalization.Away.algebraMap_isUnit (chartRatio I a b)

/--
概要：重なりで二つの指定次数のチャート分数は比 b/a の n 乗で関係付けられる。
方針：a の正則な係数像の n 乗を払い、b/a と係数 b の関係を使う。
規約：KST §5、Stacks 080Y、分子は同じ Iⁿ の元。
使われ方：一チャートのイデアル所属を他のチャートの局所化へ渡す。
-/
theorem chartOverlap_fraction (n : ℕ) (r : ↥(I ^ n)) :
    chartOverlapFromLeft I a b (chartFraction I a n r) =
      chartOverlapFromRight I a b (chartFraction I b n r) *
        chartOverlapFromLeft I a b (chartRatio I a b) ^ n := by
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_right.mp
    ((nonZeroDivisors _).pow_mem (chartOverlap_left_regular I a b) n))
  rw [sub_mul]
  apply sub_eq_zero.mpr
  calc
    _ = chartOverlapFromLeft I a b (chartBaseMap I a r.1) := by
      rw [← map_pow, ← map_mul, chartFraction_clear]
    _ = chartOverlapFromRight I a b (chartBaseMap I b r.1) := chartOverlap_base I a b r.1
    _ = chartOverlapFromRight I a b (chartFraction I b n r) *
        chartOverlapFromRight I a b (chartBaseMap I b b.1) ^ n := by
      rw [← map_pow, ← map_mul, chartFraction_clear]
    _ = chartOverlapFromRight I a b (chartFraction I b n r) *
        chartOverlapFromLeft I a b
          (chartBaseMap I a a.1 * chartRatio I a b) ^ n := by
      rw [chartBaseMap_mul_ratio, chartOverlap_base]
    _ = _ := by simp only [map_mul, mul_pow]; ring

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

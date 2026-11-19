module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartOverlapFractions
public import Mathlib.RingTheory.Localization.Ideal

/-!
概要：KST §5、Stacks 080Y の重なりで整合するチャートイデアルの分母消去。
方針：重なりの二つの拡大イデアルが一致する条件から、比の冪を掛けた所属を得る。
規約：整合性は実際の環準同型による像イデアルの等式で表す。
使われ方：中心を基底へ降ろす際に複数チャートの分子を揃える。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I : Ideal R)
  (K : ∀ a : I, Ideal (BlowupChartRing I a))

/--
概要：チャートイデアル族が実際の重なり環への拡大で一致するという条件。
方針：重なりの両係数写像による像イデアルを比較する。
規約：KST §5、Stacks 080Y、降下中心の存在そのものを仮定する条件ではない。
使われ方：斉次分子を全チャートで同時に制御する。
-/
def ChartIdealsCompatible : Prop :=
  ∀ a b : I, (K a).map (chartOverlapFromLeft I a b) =
    (K b).map (chartOverlapFromRight I a b)

/--
概要：一方のチャートに属する斉次分数は、他方で比の十分高い冪を掛けると属する。
方針：重なり上で単元である比を消去し、局所化イデアルの所属を分母消去する。
規約：KST §5、Stacks 080Y、指数はチャートと分子に依存する。
使われ方：中心の降下のための有限個の指数の共通化。
-/
theorem chart_fraction_mem_after_ratio_pow (hK : ChartIdealsCompatible I K)
    (a b : I) (n : ℕ) (r : ↥(I ^ n)) (hr : chartFraction I a n r ∈ K a) :
    ∃ m : ℕ, chartRatio I b a ^ m * chartFraction I b n r ∈ K b := by
  have hmem := Ideal.mem_map_of_mem (chartOverlapFromLeft I a b) hr
  rw [hK a b, chartOverlap_fraction] at hmem
  have hmem' := ((K b).map (chartOverlapFromRight I a b)).mul_unit_mem_iff_mem
    ((chartOverlap_left_ratio_isUnit I a b).pow n) |>.mp hmem
  let := (chartOverlapFromRight I a b).toAlgebra
  have := chartOverlap_isLocalizationRight I a b
  obtain ⟨c, ⟨m, rfl⟩, hc⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (S := BlowupOverlapRing I a b) (Submonoid.powers (chartRatio I b a))
      (K b) (chartFraction I b n r)).mp hmem'
  exact ⟨m, hc⟩

/--
概要：他方のチャートでのイデアル所属は、分子へ中心元の冪を補って達成できる。
方針：比の冪による分母消去を、次数を増した斉次分数の積公式へ戻す。
規約：KST §5、Stacks 080Y、補う元は最初のチャートの中心元 a。
使われ方：有限被覆全体で有効な同次数の分子の構成。
-/
theorem chart_fraction_mem_after_numerator_pow (hK : ChartIdealsCompatible I K)
    (a b : I) (n : ℕ) (r : ↥(I ^ n)) (hr : chartFraction I a n r ∈ K a) :
    ∃ m : ℕ, chartFraction I b (n + m)
      ⟨r.1 * a.1 ^ m, by rw [pow_add]; exact Ideal.mul_mem_mul r.2 (Ideal.pow_mem_pow a.2 m)⟩
        ∈ K b := by
  obtain ⟨m, hm⟩ := chart_fraction_mem_after_ratio_pow I K hK a b n r hr
  refine ⟨m, ?_⟩
  rw [chartFraction_mul I b n m r ⟨a.1 ^ m, Ideal.pow_mem_pow a.2 m⟩,
    chartFraction_center_pow, mul_comm]
  exact hm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

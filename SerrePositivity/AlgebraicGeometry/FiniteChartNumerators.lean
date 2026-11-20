module

public import SerrePositivity.AlgebraicGeometry.CompatibleChartIdeals

/-!
概要：KST §5、Stacks 080Y の有限個のチャートでの斉次分子の共通化。
方針：比の分母を払う指数を増加させ、有限個の最大値を取る。
規約：指数の一様性は指定した有限チャート族に対してのみ主張する。
使われ方：有限生成中心の blowup 上の中心を同じ次数で基底へ降ろす。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I : Ideal R)
  (K : ∀ a : I, Ideal (BlowupChartRing I a))

/--
概要：重なりで分母を払って得たイデアル所属は、さらに大きい比の冪でも成り立つ。
方針：最初の有効な冪へ追加の比の冪を掛ける。
規約：KST §5、Stacks 080Y、チャートと分子ごとの閾値を取る。
使われ方：有限個の所属条件の指数を揃える。
-/
theorem chart_fraction_mem_after_ratio_pow_eventually (hK : ChartIdealsCompatible I K)
    (a b : I) (n : ℕ) (r : ↥(I ^ n)) (hr : chartFraction I a n r ∈ K a) :
    ∃ N : ℕ, ∀ M ≥ N, chartRatio I b a ^ M * chartFraction I b n r ∈ K b := by
  obtain ⟨N, hN⟩ := chart_fraction_mem_after_ratio_pow I K hK a b n r hr
  refine ⟨N, fun M hM => ?_⟩
  have h := (K b).mul_mem_left (chartRatio I b a ^ (M - N)) hN
  rwa [← mul_assoc, ← pow_add, Nat.sub_add_cancel hM] at h

/--
概要：整合する有限個のチャートで、同じ冪を分子に補ってイデアル所属を達成できる。
方針：各チャートの閾値の最大値を取り、比の冪を斉次分子に戻す。
規約：KST §5、Stacks 080Y、任意に指定した有限族に対する一様性。
使われ方：一チャートの生成元を有限被覆全体で有効な分子へ移す。
-/
theorem chart_fraction_mem_on_finite_charts (hK : ChartIdealsCompatible I K)
    {ι : Type v} [Finite ι] (C : ι → I)
    (a : I) (n : ℕ) (r : ↥(I ^ n)) (hr : chartFraction I a n r ∈ K a) :
    ∃ N : ℕ, ∀ M ≥ N, ∀ i, chartFraction I (C i) (n + M)
      ⟨r.1 * a.1 ^ M, by rw [pow_add]; exact Ideal.mul_mem_mul r.2 (Ideal.pow_mem_pow a.2 M)⟩
        ∈ K (C i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose N hN using fun i =>
    chart_fraction_mem_after_ratio_pow_eventually I K hK a (C i) n r hr
  refine ⟨Finset.univ.sup N, fun M hM i => ?_⟩
  rw [chartFraction_mul I (C i) n M r ⟨a.1 ^ M, Ideal.pow_mem_pow a.2 M⟩,
    chartFraction_center_pow, mul_comm]
  exact hN i M ((Finset.le_sup (Finset.mem_univ i)).trans hM)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

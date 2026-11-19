module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartFractions

/-!
概要：KST §5、Stacks 080Y の中心の降下に使う、全チャートの条件を満たす斉次な分子。
方針：各次数で Iⁿ 内の分子の条件をイデアルとして構成し、チャート上の像を評価する。
規約：チャートイデアル族の整合性や十分大きい次数での生成は、この定義自体には仮定しない。
使われ方：中心の降下のための実際の基礎環イデアルの候補。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I : Ideal R)
  (K : ∀ a : I, Ideal (BlowupChartRing I a))

/--
概要：各チャートで指定イデアルに属する次数 n の分数の分子全体。
方針：Iⁿ への所属と全ての分数の所属を要求し、分数の加法・係数作用でイデアル性を示す。
規約：KST §5、Stacks 080Y、任意のチャートイデアル族に対し実際のイデアルを作る。
使われ方：有限生成中心の降下で大きい次数の候補中心を取る。
-/
def homogeneousNumeratorIdeal (n : ℕ) : Ideal R where
  carrier := {r | ∃ hr : r ∈ I ^ n, ∀ a : I, chartFraction I a n ⟨r, hr⟩ ∈ K a}
  zero_mem' := by
    refine ⟨(I ^ n).zero_mem, fun a => ?_⟩
    change chartFraction I a n 0 ∈ K a
    rw [chartFraction_zero]
    exact (K a).zero_mem
  add_mem' := by
    rintro r s ⟨hr, hfr⟩ ⟨hs, hfs⟩
    refine ⟨(I ^ n).add_mem hr hs, fun a => ?_⟩
    change chartFraction I a n (⟨r, hr⟩ + ⟨s, hs⟩) ∈ K a
    rw [chartFraction_add]
    exact (K a).add_mem (hfr a) (hfs a)
  smul_mem' := by
    rintro c r ⟨hr, hfr⟩
    refine ⟨(I ^ n).mul_mem_left c hr, fun a => ?_⟩
    change chartFraction I a n (c • (⟨r, hr⟩ : ↥(I ^ n))) ∈ K a
    rw [chartFraction_smul]
    exact (K a).mul_mem_left _ (hfr a)

/--
概要：次数 n の斉次な分子の候補中心は Iⁿ に含まれる。
方針：定義の所属条件を取り出す。
規約：KST §5、Stacks 080Y、有限生成性は不要。
使われ方：降下中心の支持と次数の制御。
-/
theorem homogeneousNumeratorIdeal_le (n : ℕ) : homogeneousNumeratorIdeal I K n ≤ I ^ n :=
  fun _ h => h.choose

/--
概要：分子候補中心を各チャートへ拡大すると、aⁿ 倍の指定イデアルに含まれる。
方針：分母消去式と分数の所属条件を使う。
規約：KST §5、Stacks 080Y、逆包含や十分大きい次数の生成は主張しない。
使われ方：大域の候補中心のチャート上での上界。
-/
theorem homogeneousNumeratorIdeal_map_le (n : ℕ) (a : I) :
    (homogeneousNumeratorIdeal I K n).map (chartBaseMap I a) ≤
      Ideal.span {chartBaseMap I a a.1 ^ n} * K a := by
  apply Ideal.map_le_iff_le_comap.mpr
  rintro r ⟨hr, hfr⟩
  apply Ideal.mem_span_singleton_mul.mpr
  exact ⟨chartFraction I a n ⟨r, hr⟩, hfr a,
    (mul_comm _ _).trans (chartFraction_clear I a n ⟨r, hr⟩)⟩

/--
概要：斉次な分子の候補中心へ Iᵐ を掛けると次数 n+m の候補中心に入る。
方針：二分数の積公式とチャートイデアルの乗法閉性を使う。
規約：KST §5、Stacks 080Y、チャート族の整合性を使わず成立する。
使われ方：降下中心の次数の増加と有限個の次数の共通化。
-/
theorem homogeneousNumeratorIdeal_mul_le (n m : ℕ) :
    homogeneousNumeratorIdeal I K n * I ^ m ≤ homogeneousNumeratorIdeal I K (n + m) := by
  apply Ideal.mul_le.mpr
  rintro r ⟨hr, hfr⟩ s hs
  refine ⟨by rw [pow_add]; exact Ideal.mul_mem_mul hr hs, fun a => ?_⟩
  rw [chartFraction_mul I a n m ⟨r, hr⟩ ⟨s, hs⟩]
  exact (K a).mul_mem_right _ (hfr a)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

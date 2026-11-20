module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FiniteChartNumerators

/-!
概要：KST §5、Stacks 080Y の指定チャート族を用いる斉次な分子の降下中心。
方針：指定したチャートの所属条件を満たす分子全体を実際の基礎環イデアルにする。
規約：全中心元の族と有限被覆族を区別し、量化するチャートを明示する。
使われ方：有限個のチャートで大きい次数の候補中心の生成性を証明する。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I : Ideal R)
  (K : ∀ a : I, Ideal (BlowupChartRing I a)) {ι : Type v} (C : ι → I)

/--
概要：指定チャート族上で必要なイデアルに入る次数 n の分子全体。
方針：Iⁿ への所属と各指定分数の所属を、イデアルの条件としてまとめる。
規約：KST §5、Stacks 080Y、チャート族は定義の段階では有限でなくてよい。
使われ方：有限チャート被覆で用いる基底中心の候補。
-/
def indexedNumeratorIdeal (n : ℕ) : Ideal R where
  carrier := {r | ∃ hr : r ∈ I ^ n, ∀ i, chartFraction I (C i) n ⟨r, hr⟩ ∈ K (C i)}
  zero_mem' := by
    refine ⟨(I ^ n).zero_mem, fun i => ?_⟩
    change chartFraction I (C i) n 0 ∈ K (C i)
    rw [chartFraction_zero]
    exact (K (C i)).zero_mem
  add_mem' := by
    rintro r s ⟨hr, hfr⟩ ⟨hs, hfs⟩
    refine ⟨(I ^ n).add_mem hr hs, fun i => ?_⟩
    change chartFraction I (C i) n (⟨r, hr⟩ + ⟨s, hs⟩) ∈ K (C i)
    rw [chartFraction_add]
    exact (K (C i)).add_mem (hfr i) (hfs i)
  smul_mem' := by
    rintro c r ⟨hr, hfr⟩
    refine ⟨(I ^ n).mul_mem_left c hr, fun i => ?_⟩
    change chartFraction I (C i) n (c • (⟨r, hr⟩ : ↥(I ^ n))) ∈ K (C i)
    rw [chartFraction_smul]
    exact (K (C i)).mul_mem_left _ (hfr i)

/--
概要：指定チャート族の分子候補中心は Iⁿ に含まれる。
方針：定義の最初の所属条件を使う。
規約：KST §5、Stacks 080Y、有限性は不要。
使われ方：候補中心の冪次数と支持の制御。
-/
theorem indexedNumeratorIdeal_le (n : ℕ) : indexedNumeratorIdeal I K C n ≤ I ^ n :=
  fun _ h => h.choose

/--
概要：候補中心の各指定チャートへの像は aⁿ 倍の指定イデアルに含まれる。
方針：分子の所属と分母消去式を使う。
規約：KST §5、Stacks 080Y、指定チャートの添字を明示する。
使われ方：十分大きい次数での像イデアルの等式の順包含。
-/
theorem indexedNumeratorIdeal_map_le (n : ℕ) (i : ι) :
    (indexedNumeratorIdeal I K C n).map (chartBaseMap I (C i)) ≤
      Ideal.span {chartBaseMap I (C i) (C i).1 ^ n} * K (C i) := by
  apply Ideal.map_le_iff_le_comap.mpr
  rintro r ⟨hr, hfr⟩
  exact Ideal.mem_span_singleton_mul.mpr
    ⟨chartFraction I (C i) n ⟨r, hr⟩, hfr i,
      (mul_comm _ _).trans (chartFraction_clear I (C i) n ⟨r, hr⟩)⟩

/--
概要：一チャートのイデアルの元は、十分大きい各次数で有限族全体の分子候補から表される。
方針：元を一つの分数で表し、有限族に対する共通の分子補正を使う。
規約：KST §5、Stacks 080Y、元のチャートは指定族の一員でなくてもよい。
使われ方：有限生成元を大きい同じ次数で候補中心へ入れる。
-/
theorem indexedNumerator_represents_eventually [Finite ι]
    (hK : ChartIdealsCompatible I K) (a : I) (z : BlowupChartRing I a) (hz : z ∈ K a) :
    ∃ N : ℕ, ∀ D ≥ N, ∃ r : ↥(I ^ D), r.1 ∈ indexedNumeratorIdeal I K C D ∧
      chartFraction I a D r = z := by
  obtain ⟨n, r, heq⟩ := exists_chartFraction I a z
  obtain ⟨N, hN⟩ := chart_fraction_mem_on_finite_charts I K hK C a n r
    (heq.symm ▸ hz)
  refine ⟨n + N, fun D hD => ?_⟩
  let M := D - n
  have hM : N ≤ M := by dsimp only [M]; omega
  have he : n + M = D := by dsimp only [M]; omega
  have hsome : ∃ s : ↥(I ^ (n + M)), s.1 ∈ indexedNumeratorIdeal I K C (n + M) ∧
      chartFraction I a (n + M) s = z := by
    refine ⟨⟨r.1 * a.1 ^ M,
      by rw [pow_add]; exact Ideal.mul_mem_mul r.2 (Ideal.pow_mem_pow a.2 M)⟩,
      ⟨_, hN M hM⟩, ?_⟩
    exact (chartFraction_shift_self I a n M r).trans heq
  let P (d : ℕ) : Prop := ∃ s : ↥(I ^ d), s.1 ∈ indexedNumeratorIdeal I K C d ∧
    chartFraction I a d s = z
  exact (congrArg P he).mp hsome

/--
概要：有限個の整合する有限生成チャートイデアルは、十分大きい各次数で一つの分子候補中心から生成される。
方針：全チャートの有限生成元を有限の直和型で束ね、各元を表す次数の最大値を取る。
規約：KST §5、Stacks 080Y、像イデアルは aᴰ 倍の指定イデアルと等しい。
使われ方：有限チャート被覆を用いる中心の実際の降下。
-/
theorem indexedNumeratorIdeal_map_eventually [Finite ι]
    (hK : ChartIdealsCompatible I K) (hfg : ∀ i, (K (C i)).FG) :
    ∃ N : ℕ, ∀ D ≥ N, ∀ i,
      (indexedNumeratorIdeal I K C D).map (chartBaseMap I (C i)) =
        Ideal.span {chartBaseMap I (C i) (C i).1 ^ D} * K (C i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose s hs using hfg
  let τ := Σ i, ↥(s i)
  have hmem (p : τ) : p.2.1 ∈ K (C p.1) := by
    rw [← hs p.1]
    exact Ideal.subset_span p.2.2
  choose N hN using fun p : τ =>
    indexedNumerator_represents_eventually I K C hK (C p.1) p.2.1 (hmem p)
  let : Fintype τ := Fintype.ofFinite τ
  refine ⟨Finset.univ.sup N, fun D hD i =>
    le_antisymm (indexedNumeratorIdeal_map_le I K C D i) ?_⟩
  rw [← hs i, Ideal.span_mul_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨c, hc, z, hz, rfl⟩
  obtain rfl := Set.mem_singleton_iff.mp hc
  dsimp only
  obtain ⟨r, hr, heq⟩ := hN ⟨i, ⟨z, hz⟩⟩ D
    ((Finset.le_sup (Finset.mem_univ ⟨i, ⟨z, hz⟩⟩)).trans hD)
  dsimp only at heq
  rw [← heq, mul_comm, chartFraction_clear]
  exact Ideal.mem_map_of_mem _ hr

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

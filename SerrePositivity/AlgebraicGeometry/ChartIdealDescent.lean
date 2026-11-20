module

public import SerrePositivity.AlgebraicGeometry.ChartEmbedding

/-!
概要：KST §5、Stacks 080Y の中心の降下に使う標準 blowup チャート上の有限分母消去。
方針：各斉次分母の指数を有限個の最大値に揃え、分子を中心の同じ冪に入れる。
規約：チャート内の等式を用い、基礎環で中心元の正則性を仮定しない。
使われ方：チャート上の有限生成イデアルを基礎環のイデアルの拡大として記述する準備。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)

/--
概要：標準チャート上の有限個の元の分母を、中心の同じ冪の分子で一斉に払える。
方針：各元の分母指数の最大値を取り、足りない指数を分子へ補う。
規約：KST §5、Stacks 080Y、空族も n = 0 により含む。
使われ方：チャート上の有限生成イデアルの降下。
-/
theorem chart_finite_clear_denominators {ι : Type v} [Finite ι]
    (z : ι → BlowupChartRing I a) :
    ∃ (N : ℕ) (r : ι → R), (∀ i, r i ∈ I ^ N) ∧
      ∀ i, chartBaseMap I a (r i) = z i * chartBaseMap I a a.1 ^ N := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose n r hr hz using fun i => chart_clear_denominator_mem I a (z i)
  let N := Finset.univ.sup n
  have hn (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N, fun i => r i * a.1 ^ (N - n i), ?_, ?_⟩
  · intro i
    have h := Ideal.mul_mem_mul (hr i) (Ideal.pow_mem_pow a.2 (N - n i))
    rwa [← pow_add, Nat.add_sub_of_le (hn i)] at h
  · intro i
    rw [map_mul, map_pow, ← hz i, mul_assoc, ← pow_add, Nat.add_sub_of_le (hn i)]

/--
概要：チャート上の有限生成イデアルは、生成元の冪を掛けると基礎環のイデアルから拡大される。
方針：有限生成元の分母を一斉に払い、その分子が生成する基礎環のイデアルを取る。
規約：KST §5、Stacks 080Y、降ろしたイデアルは I の同じ冪に含まれる。
使われ方：blowup 上の中心を基底へ降ろすための一チャート上の入力。
-/
theorem chart_finite_ideal_descent (K : Ideal (BlowupChartRing I a)) (hK : K.FG) :
    ∃ (N : ℕ) (J : Ideal R), J ≤ I ^ N ∧
      J.map (chartBaseMap I a) = Ideal.span {chartBaseMap I a a.1 ^ N} * K := by
  classical
  obtain ⟨s, hs⟩ := hK
  obtain ⟨N, r, hr, heq⟩ := chart_finite_clear_denominators I a
    (fun z : s => z.1)
  let J := Ideal.span (Set.range r)
  refine ⟨N, J, Ideal.span_le.mpr (Set.range_subset_iff.mpr hr), ?_⟩
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨z.1, ?_, ?_⟩
    · rw [← hs]
      exact Ideal.subset_span z.2
    · rw [heq z, mul_comm]
  · rw [← hs, Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨c, hc, z, hz, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp hc
    dsimp only
    rw [mul_comm, ← heq ⟨z, hz⟩]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨⟨z, hz⟩, rfl⟩)

/--
概要：有限生成イデアルの一チャート上の降下は、十分大きい任意の次数で可能。
方針：最初に分母を払ったイデアルへ中心の追加の冪を掛ける。
規約：KST §5、Stacks 080Y、各次数の降下イデアルは I のその次数の冪に含まれる。
使われ方：有限個のチャートで中心の降下の次数を揃える。
-/
theorem chart_finite_ideal_descent_eventually (K : Ideal (BlowupChartRing I a)) (hK : K.FG) :
    ∃ N : ℕ, ∀ M ≥ N, ∃ J : Ideal R, J ≤ I ^ M ∧
      J.map (chartBaseMap I a) = Ideal.span {chartBaseMap I a a.1 ^ M} * K := by
  obtain ⟨N, J, hJle, hJ⟩ := chart_finite_ideal_descent I a K hK
  refine ⟨N, fun M hM => ⟨J * I ^ (M - N), ?_, ?_⟩⟩
  · calc
      _ ≤ I ^ N * I ^ (M - N) := Ideal.mul_mono_left hJle
      _ = I ^ M := by rw [← pow_add, Nat.add_sub_of_le hM]
  · rw [Ideal.map_mul, hJ, Ideal.map_pow, chart_map_ideal_eq_span, Ideal.span_singleton_pow]
    calc
      _ = (Ideal.span {chartBaseMap I a a.1 ^ N} *
          Ideal.span {chartBaseMap I a a.1 ^ (M - N)}) * K := by
        rw [mul_assoc, Ideal.mul_comm K _, ← mul_assoc]
      _ = _ := by
        rw [Ideal.span_singleton_mul_span_singleton, ← pow_add, Nat.add_sub_of_le hM]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

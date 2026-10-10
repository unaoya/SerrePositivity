module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Data.List.OfFn

/-!
# 正則パラメータの正則性という未証明入力

正則局所環の極大イデアルを次元と同数の元で生成すると正則列になる、という
標準定理だけを名前付きの `sorry` として残す。最小生成列の存在は Mathlib の
`spanFinrank` の定理から導き、正則性を得る箇所でこの入力を直接呼ぶ。

この入力を独立させることで、整域性・有限自由分解の存在・Euler 標数の計算が
循環 import なしに同じ未証明入力を共有する。整域性と分解の構成そのものは、
正則生成列を仮定する一般定理として別途証明されている。
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

/-- 正則局所環の極大イデアルの最小生成列を選ぶ。
生成元の個数が Krull 次元に等しいことは Mathlib の定義から従う。
この列の正則性に限って、名前付きの未証明定理を明示的に適用する。 -/
lemma exists_regular_generators (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    ∃ rs : List R, RingTheory.Sequence.IsWeaklyRegular R rs ∧
      Ideal.ofList rs = maximalIdeal R ∧ ringKrullDim R = rs.length := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  let z : Fin s.toList.length → R := s.toList.get
  have hz : Ideal.span (Set.range z) = maximalIdeal R := by
    simpa [z] using hspan
  have hd : ringKrullDim R = s.toList.length := by
    simpa [hcard] using (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  refine ⟨s.toList, ?_, ?_, hd⟩
  · simpa only [z, List.ofFn_get] using isWeaklyRegular_of_span_eq_maximalIdeal R z hz hd
  · simpa [Ideal.ofList] using hspan

end SerrePositivity

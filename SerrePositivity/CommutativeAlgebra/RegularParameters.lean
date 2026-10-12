module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Data.List.OfFn
public import SerrePositivity.CommutativeAlgebra.RegularParametersProof

/-!
# 正則パラメータと最小生成列

正則局所環の極大イデアルを次元と同数の元で生成すると正則列になる、という
標準定理を `RegularParametersProof.lean` の証明から公開する。随伴次数環の
多項式表示の単射性を Samuel 次元定理で導き、Krull の共通部分定理により
生成元の正則性を得る。先頭による商の次元と生成元を計算し、列の長さに帰納する。

最小生成列の存在は Mathlib の `spanFinrank` の定理から導く。
整域性・有限自由分解・Euler 標数の計算が参照する既存の公開名を保つ。
-/

@[expose] public section

universe u
open IsLocalRing
namespace SerrePositivity

/-- 正則局所環 `A` で、`z = (z_1, …, z_e)` が `m_A` を生成し `e = dim A` なら、
`z` は弱正則列（各 `z_i` が `A/(z_1, …, z_{i-1})` の非零因子）。正則局所環の正則パラメータ系が
正則列であるという標準的な事実。 -/
theorem isWeaklyRegular_of_span_eq_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {e : ℕ} (z : Fin e → A) (hz : Ideal.span (Set.range z) = maximalIdeal A)
    (he : ringKrullDim A = e) : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z) :=
  isWeaklyRegular_of_minimal_generators A z hz he

/-- 正則局所環の極大イデアルの最小生成列を選ぶ。
生成元の個数が Krull 次元に等しいことは Mathlib の定義から従う。
この列の正則性は、上の証明済み定理を適用して得る。 -/
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

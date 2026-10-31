module

public import SerrePositivity.Asymptotic.PaperRankQuotient
public import SerrePositivity.CategoryTheory.ScalarSupport

/-! # 根基が同じパラメータ系への支持の変更

第二比較で有限近似側と正則基底側のパラメータを照合するための支持条件。
ランク商・冪等完備化の後の恒等射について、共通の線形圏の補題を適用する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {e f : ℕ} (z : Fin e → R) (w : Fin f → R)

/-- ランク商での支持を、生成イデアルの根基の包含に沿って変更する。 -/
lemma paperSupportedRank_of_span_le_radical
    (h : Ideal.span (Set.range w) ≤ (Ideal.span (Set.range z)).radical)
    {X : PaperRankQuotient R s} (hX : paperSupportedRank z X) : paperSupportedRank w X :=
  scalarSupported_of_span_le_radical z w h hX

/-- 根基が等しければ、論文の支持圏はパラメータ系によらない。 -/
lemma paperSupportedRank_eq_of_radical_eq
    (h : (Ideal.span (Set.range z)).radical = (Ideal.span (Set.range w)).radical) :
    paperSupportedRank (s := s) z = paperSupportedRank w :=
  scalarSupported_eq_of_radical_eq z w h

end SerrePositivity.Asymptotic

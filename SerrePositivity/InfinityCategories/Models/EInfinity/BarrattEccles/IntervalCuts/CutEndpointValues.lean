module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FactorBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.DeletedOutputVertices

/-!
模型。文献の定義との比較は後で
# 辺の端点置換テンソルと実際の削除語の切断値

概要：Berger–Fresse §2.2.7 の各辺の端点境界を削除語の実際の出力テンソルへ同定する。
方針：既存の全出力族の置換公式を、指定整数次数のテンソル生成元へ適用する。
規約：全ての元は元の非零切断の境界次数に置く。
使われ方：スカラー符号の一致と組み合わせ、反復色の削除項を境界項へ戻す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非零切断で反復する色の出力因子は辺（BF §2.2.1）。
方針：二出現の前の位置は活動位置なので、その色は出力辺となる。
規約：指定位置は前・後のどちらの出現でもよい。
使われ方：反復色の因子へ端点置換テンソルを適用する。 -/
lemma edgeOutput_repeat_color {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (i : Fin (n + d))
    (hr : ∃ j, j ≠ i ∧ u.val j = u.val i) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p (u.val i) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u p h]
  obtain ⟨j, hji, huj⟩ := hr
  rcases lt_or_gt_of_ne hji with hj | hj
  · exact ⟨j, Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨i, hj, huj.symm⟩⟩)), huj⟩
  · exact ⟨i, Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨j, hj, huj⟩⟩)), rfl⟩

variable (A : Type u) [CommRing A]

/-- 概要：左出現削除の切断テンソルは元の色の終点置換テンソル（BF §2.2.7）。
方針：削除後の全出力族と端点置換族の一致を実際の反復テンソルへ渡す。
規約：削除後の次数 d+1 を元の境界整数次数へ移す。
使われ方：左削除の符号付き値と辺の終点境界項の比較。 -/
lemma endpointTensor_eraseCut_left {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val (i.succAbove q)) (hi : i < i.succAbove q)
    (hr : ∃ j, j ≠ i ∧ u.val j = u.val i) :
    let v := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.eraseCutBasisWord u (i.succAbove q) i h (ne_of_lt hi) hr
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u (i.succAbove q)) (u.val i)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_repeat_color u (i.succAbove q) h i hr) 1 =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput v q)
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u (i.succAbove q)) : ℤ) + 1) (by
          have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u (i.succAbove q) h
          have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree v q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_edgeNondegenerate u.val i q h)
          omega) := by
  dsimp only
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_congr
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eraseCut_left u i q h hi hr).symm

/-- 概要：右出現削除の切断テンソルは元の色の始点置換テンソル（BF §2.2.7）。
方針：削除後の全出力族と始点置換族の一致を反復テンソルへ渡す。
規約：両方の値を元の非零切断の境界次数に置く。
使われ方：右削除の符号付き値と辺の始点境界項の比較。 -/
lemma endpointTensor_eraseCut_right {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val (i.succAbove q)) (hi : i.succAbove q < i)
    (hr : ∃ j, j ≠ i ∧ u.val j = u.val i) :
    let v := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.eraseCutBasisWord u (i.succAbove q) i h (ne_of_gt hi) hr
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u (i.succAbove q)) (u.val i)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_repeat_color u (i.succAbove q) h i hr) 0 =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput v q)
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u (i.succAbove q)) : ℤ) + 1) (by
          have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u (i.succAbove q) h
          have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree v q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_edgeNondegenerate u.val i q h)
          omega) := by
  dsimp only
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_congr
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eraseCut_right u i q h hi hr).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

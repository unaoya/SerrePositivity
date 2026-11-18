module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatPairFibers
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeDifferentialExpansion

/-!
模型。文献の定義との比較は後で
# 元切断非零の全削除和と反復色全因子境界和

概要：Berger–Fresse §2.2.7 の元切断非零部分を実際の反復色因子境界の全和へ同定する。
方針：左右二削除の有限同値で二項をまとめ、反復位置対を非零切断と区切りへ移す。
規約：二種類の障害部分は既存の三部分比較で全て処理する。
使われ方：実際の削除微分を全因子境界和へ戻す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：元切断非零の全削除和は全反復位置対の実際の因子境界和（BF §2.2.7）。
方針：位置対・削除側の有限同値で和を移し、側零と一の二項を因子境界へまとめる。
規約：全ての実際の正規化削除値を含む。
使われ方：全微分保存の元切断非零部分。 -/
lemma normalizedDeletedValue_sum_regular_pairs {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) :
    (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u.val, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c.val) =
      ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatCutPair u.val,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.factorBoundaryValue A u c.pivot c.nondegenerate (u.val c.left) := by
  classical
  rw [← (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.regularCutEquiv u).sum_comp (fun c => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c.val),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fin.sum_univ_two]
  exact (c.factorBoundary_eq_pair A u).symm

/-- 概要：元切断非零の全削除和は非零元切断ごとの区切り因子境界和（BF §2.2.7）。
方針：全反復位置対を非零切断と区切りの依存組へ移す。
規約：各区切り色は一つの反復色に対応する。
使われ方：切断点色境界和と合わせて全活動位置境界へ戻す。 -/
lemma normalizedDeletedValue_sum_regular {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) :
    (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u.val, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c.val) =
      ∑ p : {p : Fin (n + (d + 1)) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
        ∑ a : {a : Fin (n + (d + 1)) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val a},
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.factorBoundaryValue A u p.val p.property (u.val a.val) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue_sum_regular_pairs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_repeatPair_factorBoundary]

/-- 概要：実際の削除微分の辺成分は全反復色因子境界と全切断点色境界の和（BF §2.2.7）。
方針：二障害部分の処理に元切断非零部分の全因子境界比較を代入する。
規約：削除項の未処理部分を残さない。
使われ方：出力テンソルの全境界との最終照合。 -/
lemma edgeComponent_differentialOnWord_factor_sums {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord A u) =
      (∑ p : {p : Fin (n + (d + 1)) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
        ∑ a : {a : Fin (n + (d + 1)) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val a},
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.factorBoundaryValue A u p.val p.property (u.val a.val)) +
        ∑ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_differentialOnWord_reduce, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue_sum_regular]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

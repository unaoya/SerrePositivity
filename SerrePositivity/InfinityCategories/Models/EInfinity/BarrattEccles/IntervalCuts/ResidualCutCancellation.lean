module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutOutputs

/-!
模型。文献の定義との比較は後で
# 非切断点障害を持つ全削除切断項の相殺

概要：Berger–Fresse §2.2.7 の余分な削除和の非切断点障害部分は零となる。
方針：交換対で値が同じで係数が反対になることを、固定点なし対合の和へ適用する。
規約：任意の可換環上の実際の正規化区間テンソルを使う。
使われ方：χ の区間切断作用の微分保存から余分な項を取り除く。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：交換で値を保つ任意の加法群値に対し、削除係数付き二項は相殺（BF §2.2.7）。
方針：係数反対性と値の一致を整数倍へ渡す。
規約：加法群の二での除算や無捩れ性は使わない。
使われ方：任意の可換環上の区間テンソルの二項相殺。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.weighted_pair {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) {M : Type*} [AddCommGroup M]
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u → M) (hv : v c = v c.swap) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u c.deleted * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.deleted) c.pivot) • v c +
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u c.swap.deleted *
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.swap.deleted) c.swap.pivot) • v c.swap = 0 := by
  rw [c.swap_coefficient, hv, neg_smul, neg_add_cancel]

/-- 概要：交換で値を保つ全非切断点障害項の削除係数付き有限和は零（BF §2.2.7）。
方針：固定点なし対合で二項を対にして和を取る。
規約：任意の可換加法群に成立する。
使われ方：実際の区間テンソルと将来の同型表示のどちらにも使う。 -/
lemma nonpivotResidualCut_weighted_sum {n l : ℕ} {u : Fin (l + 1) → Fin n}
    {M : Type*} [AddCommGroup M] (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u → M)
    (hv : ∀ c, v c = v c.swap) :
    ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u,
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u c.deleted * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.deleted) c.pivot) • v c = 0 := by
  classical
  exact Finset.sum_ninvolution _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.swap (fun c => c.weighted_pair v (hv c))
    (fun c _ => c.swap_ne) (fun _ => Finset.mem_univ _) _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.swap_swap

/-- 概要：実際の正規化区間テンソルに値を取る全非切断点障害項は相殺（BF §2.2.7）。
方針：削除基底語のテンソル値の交換不変性を一般の重み付き和へ代入する。
規約：元次数 d+1 の語を削除し、出力次数 d+1 で全てを加える。
使われ方：χ の辺に対する作用の微分保存の余分項を消す。 -/
lemma residualCut_tensor_sum_eq_zero (A : Type u) [CommRing A] {n d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) :
    ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u.val,
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val c.deleted * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val c.deleted) c.pivot) •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residualCutBasisWord u c) c.pivot)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ c.nondegenerate) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nonpivotResidualCut_weighted_sum _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residualCut_tensor_eq A u)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

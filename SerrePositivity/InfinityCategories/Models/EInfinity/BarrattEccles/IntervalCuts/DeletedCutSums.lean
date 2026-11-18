module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.DeletedCutEquivalences
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutCancellation
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotBoundaryComparison

/-!
模型。文献の定義との比較は後で
# 正規化全削除和の三部分分割と二障害部分の処理

概要：Berger–Fresse §2.2.7 の正規化全削除和を元切断非零・二障害部分へ分ける。
方針：三条件の排反性で有限和を分割し、既存の有限同値を通して相殺と境界比較を適用する。
規約：全て実際の正規化区間テンソルに値を取る。
使われ方：元切断非零部分の因子境界比較だけを残す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

private lemma sum_ite_subtype {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (v : α → M) :
    (∑ a, if P a then v a else 0) = ∑ a : {a // P a}, v a.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun _ => by simp) v

/-- 概要：正規化削除切断の任意の和は元切断非零と二障害部分の三和（BF §2.2.7）。
方針：元切断の非零性と削除色・切断点色の一致を順に分ける。
規約：値は任意の可換加法モノイドでよい。
使われ方：三種類の実際の削除項の統合。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.sum_three {n l : ℕ} {u : Fin (l + 1) → Fin n}
    {M : Type*} [AddCommMonoid M] (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u → M) :
    ∑ c, v c = (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u, v c.val) +
      (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Nonpivot u, v c.val) +
        ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Pivot u, v c.val := by
  classical
  let R (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (c.deleted.succAbove c.pivot)
  let P (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u) := u c.deleted = u (c.deleted.succAbove c.pivot)
  have hsum : ∑ c, v c = ∑ c,
      ((if R c then v c else 0) + (if ¬ R c ∧ ¬ P c then v c else 0) +
        (if P c then v c else 0)) := by
    apply Finset.sum_congr rfl
    intro c _
    by_cases hr : R c
    · have hp : ¬ P c := fun hp => Fin.ne_succAbove c.deleted c.pivot
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique hr c.deleted hp)
      simp only [hr, hp, not_true_eq_false, false_and, ite_true, ite_false, add_zero]
    · by_cases hp : P c <;>
        simp only [hr, hp, not_false_eq_true, not_true_eq_false, and_self, true_and,
          ite_true, ite_false, zero_add, add_zero]
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_ite_subtype R v, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_ite_subtype (fun c => ¬ R c ∧ ¬ P c) v, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_ite_subtype P v]

variable (A : Type u) [CommRing A]

/-- 概要：正規化削除切断の実際の符号付きテンソル値（BF §1.2.3・§2.2.7）。
方針：共通の実際の削除基底語を評価し、削除係数と切断符号を掛ける。
規約：元次数 d+1 と出力次数 d+1。
使われ方：三部分を同じ成分で加える。 -/
def normalizedDeletedValue {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u.val) : (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-((d + 1 : ℕ) : ℤ)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val c.deleted * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val c.deleted) c.pivot) •
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.word u c) c.pivot)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ c.nondegenerate)

/-- 概要：正規化全削除和の非切断点障害部分は零（BF §2.2.7）。
方針：既存の対合添字との有限同値を通して実際の全和相殺を適用する。
規約：元切断非零部分はここに含まない。
使われ方：三部分分割の第二部分を消す。 -/
lemma normalizedDeletedValue_sum_nonpivot {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) :
    ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Nonpivot u.val, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c.val = 0 := by
  rw [← (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.nonpivotEquiv u).sum_comp
    (fun c => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c.val)]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residualCut_tensor_sum_eq_zero A u

/-- 概要：正規化全削除和の切断点障害部分は切断点色の全因子境界和（BF §2.2.7）。
方針：既存の切断点障害添字との有限同値を通して全境界比較を適用する。
規約：退化元切断の部分を実際のテンソル値で比較する。
使われ方：三部分分割の第三部分を処理する。 -/
lemma normalizedDeletedValue_sum_pivot {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) :
    ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Pivot u.val, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c.val =
      ∑ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p := by
  rw [← (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.pivotEquiv u).sum_comp
    (fun c => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c.val)]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotResidualValue_sum_eq_boundary A u

/-- 概要：正規化全削除和は元切断非零部分と切断点色全因子境界和の和（BF §2.2.7）。
方針：三部分分割へ非切断点相殺と切断点全境界比較を代入する。
規約：全ての arity・正次数の語を扱う。
使われ方：残る反復色因子境界と元切断非零部分の比較へ帰着する。 -/
lemma normalizedDeletedValue_sum_reduce {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) :
    ∑ c, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c =
      (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u.val, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c.val) +
        ∑ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.sum_three, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue_sum_nonpivot,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue_sum_pivot, add_zero]

/-- 概要：元の非零切断が一つもなければ正規化全削除和も零（BF §2.2.7）。
方針：三部分の統合で残った元切断非零部分と切断点色境界和をともに零にする。
規約：二種類の障害項は全て含めたまま相殺する。
使われ方：辺成分が零となる語の微分保存。 -/
lemma normalizedDeletedValue_sum_eq_zero_of_no_cut {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (h : ∀ p, ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) : ∑ c, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue_sum_reduce]
  have hr : (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.Regular u.val, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.normalizedDeletedValue A u c.val) = 0 :=
    Finset.sum_eq_zero (fun c _ => False.elim (h _ c.property))
  rw [hr, zero_add]
  apply Finset.sum_eq_zero
  intro p _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue, dite_eq_right (h p)]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

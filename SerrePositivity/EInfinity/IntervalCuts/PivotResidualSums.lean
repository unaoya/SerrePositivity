module

public import SerrePositivity.EInfinity.IntervalCuts.PivotResidualEquivalences
public import SerrePositivity.EInfinity.IntervalCuts.PivotDeletionValues

/-!
# 切断点障害の全削除和の隙間への添字替え

概要：Berger–Fresse §2.2.7 の全切断点障害削除値を隣接退化切断の隙間和へ移す。
方針：有限添字を左右に分け、各有限同値と実際の重み付き値の公式を使う。
規約：実際の区間テンソルの同じ次数で全てを加える。
使われ方：切断点色の全境界和との比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：有限添字で保持した切断点障害の実際の符号付き削除値（BF §2.2.7）。
方針：実際の削除基底語を評価し、削除係数と切断符号を掛ける。
規約：元次数 d+1 と出力次数 d+1 を保つ。
使われ方：χ の微分の切断点障害部分の有限和。 -/
def pivotResidualValue {n d : ℕ} (u : BasisWord n (d + 1)) (c : PivotResidualCut u.val) :
    (power (interval A) n).X (-((d + 1 : ℕ) : ℤ)) :=
  (deletionCoefficient u.val c.deleted * edgeSign (erase u.val c.deleted) c.pivot) •
    tensorVectorOfDegree A n (d + 1)
      (edgeOutput (pivotEraseBasisWord u c.deleted c.pivot c.nondegenerate c.same_color) c.pivot)
      (edgeOutput_tupleDegree _ _ c.nondegenerate)

/-- 概要：全左削除和は直前隙間が非退化な退化切断上の負の隙間和（BF §2.2.7）。
方針：左有限同値で添字を替え、各項の実際の重み付き値を比較する。
規約：元の非零辺切断の存在は不要。
使われ方：全削除和の左部分。 -/
lemma pivotResidualValue_sum_before {n d : ℕ} (u : BasisWord n (d + 1)) :
    ∑ c : PivotResidualCut.Before u.val, pivotResidualValue A u c.val =
      ∑ p : PivotResidualCut.BeforeCut u.val,
        -(((-1 : ℤ) ^ (Finset.univ.filter (Caesura u.val)).card *
            (-1 : ℤ) ^ positionInversionCount u.val (Finset.univ.filter (Caesura u.val))) •
          gapTensor A u p.val.castSucc) := by
  apply Fintype.sum_equiv PivotResidualCut.beforeEquiv
  intro c
  exact pivotDeletion_weighted_before A u c.val.deleted c.val.pivot
    c.val.nondegenerate c.val.same_color c.property

/-- 概要：全右削除和は直後隙間が非退化な退化切断上の正の隙間和（BF §2.2.7）。
方針：右有限同値で添字を替え、各項の実際の重み付き値を比較する。
規約：元の非零辺切断の存在は不要。
使われ方：全削除和の右部分。 -/
lemma pivotResidualValue_sum_after {n d : ℕ} (u : BasisWord n (d + 1)) :
    ∑ c : PivotResidualCut.After u.val, pivotResidualValue A u c.val =
      ∑ p : PivotResidualCut.AfterCut u.val,
        ((-1 : ℤ) ^ (Finset.univ.filter (Caesura u.val)).card *
            (-1 : ℤ) ^ positionInversionCount u.val (Finset.univ.filter (Caesura u.val))) •
          gapTensor A u p.val.succ := by
  apply Fintype.sum_equiv PivotResidualCut.afterEquiv
  intro c
  exact pivotDeletion_weighted_after A u c.val.deleted c.val.pivot
    c.val.nondegenerate c.val.same_color c.property

/-- 概要：全切断点障害削除和は共通係数付きの二つの隙間和の差（BF §2.2.7）。
方針：左右分割と両有限同値を使い、共通係数を和の外へ出す。
規約：元の全切断が退化する場合も含む無条件な全有限和。
使われ方：切断点色の全因子境界和との比較。 -/
lemma pivotResidualValue_sum {n d : ℕ} (u : BasisWord n (d + 1)) :
    ∑ c, pivotResidualValue A u c =
      ((-1 : ℤ) ^ (Finset.univ.filter (Caesura u.val)).card *
          (-1 : ℤ) ^ positionInversionCount u.val (Finset.univ.filter (Caesura u.val))) •
        ((∑ p : PivotResidualCut.AfterCut u.val, gapTensor A u p.val.succ) -
          ∑ p : PivotResidualCut.BeforeCut u.val, gapTensor A u p.val.castSucc) := by
  rw [PivotResidualCut.sum_split, pivotResidualValue_sum_before, pivotResidualValue_sum_after]
  simp only [Finset.sum_neg_distrib, ← Finset.smul_sum, smul_sub]
  exact neg_add_eq_sub _ _

end SerrePositivity.EInfinity.IntervalCuts

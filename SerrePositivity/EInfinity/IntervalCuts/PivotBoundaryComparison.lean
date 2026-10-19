module

public import SerrePositivity.EInfinity.IntervalCuts.GapSumBalance
public import SerrePositivity.EInfinity.IntervalCuts.PivotResidualSums
public import SerrePositivity.EInfinity.IntervalCuts.PivotBoundarySum

/-!
# 切断点障害全削除和と切断点色全因子境界和の一致

概要：Berger–Fresse §2.2.7 の正次数の切断点障害全削除和は実際の切断点色全境界和に一致する。
方針：有限同値で隙間和へ移し、非零切断と退化切断の補集合の釣り合いを使う。
規約：先頭前・末尾後は正次数で零。元の非零辺切断がない場合も含む。
使われ方：χ の区間切断作用の微分保存の切断点部分を閉じる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open scoped BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：正次数の先頭前の実際の隙間テンソル値は零（BF §2.2.7）。
方針：全出力は一頂点なので総次数零となり、正の指定次数に合わない。
規約：arity 零も含む。
使われ方：全隙間和の先頭境界を消す。 -/
lemma gapTensor_first_positive {n d : ℕ} (u : BasisWord n (d + 1)) :
    gapTensor A u 0 = 0 := by
  have hd : tupleDegree n (gapOutput u 0) = 0 := by
    rw [gapOutput_first u]
    exact vertex_tupleDegree n 1
  have hn : ¬ tupleDegree n (gapOutput u 0) = d + 1 := by rw [hd]; omega
  simp only [gapTensor, dite_eq_right hn]

/-- 概要：正次数の末尾後の実際の隙間テンソル値は零（BF §2.2.7）。
方針：全出力は零頂点なので総次数零となり、正の指定次数に合わない。
規約：arity 零も含む。
使われ方：全隙間和の末尾境界を消す。 -/
lemma gapTensor_last_positive {n d : ℕ} (u : BasisWord n (d + 1)) :
    gapTensor A u (Fin.last (n + (d + 1))) = 0 := by
  have hd : tupleDegree n (gapOutput u (Fin.last (n + (d + 1)))) = 0 := by
    rw [gapOutput_last u]
    exact vertex_tupleDegree n 0
  have hn : ¬ tupleDegree n (gapOutput u (Fin.last (n + (d + 1)))) = d + 1 := by
    rw [hd]
    omega
  simp only [gapTensor, dite_eq_right hn]

/-- 概要：切断点色の全境界和は非零切断上の共通係数付き隙間差和（BF §2.2.7）。
方針：退化項を零として除き、非零切断の実際の隙間差公式を全て足す。
規約：全ての語次数を扱う。
使われ方：隙間の補集合和と実際の因子境界和を接続する。 -/
lemma pivotBoundaryValue_sum_subtype {n d : ℕ} (u : BasisWord n d) :
    ∑ p, pivotBoundaryValue A u p =
      ((-1 : ℤ) ^ (Finset.univ.filter (Caesura u.val)).card *
          (-1 : ℤ) ^ positionInversionCount u.val (Finset.univ.filter (Caesura u.val))) •
        ∑ p : {p : Fin (n + d) // EdgeNondegenerate u.val p},
          (gapTensor A u p.val.castSucc - gapTensor A u p.val.succ) := by
  classical
  calc
    _ = ∑ p : {p : Fin (n + d) // EdgeNondegenerate u.val p},
        pivotBoundaryValue A u p.val := by
      calc
        _ = ∑ p ∈ Finset.univ.filter (EdgeNondegenerate u.val), pivotBoundaryValue A u p := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro p _ hp
          have hn : ¬ EdgeNondegenerate u.val p := fun h => hp
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          simp only [pivotBoundaryValue, dite_eq_right hn]
        _ = _ := Finset.sum_subtype _ (fun _ => by simp) _
    _ = _ := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p _
      exact pivotBoundaryValue_eq A u p.val p.property

/-- 概要：正次数の実際の全切断点障害削除和は全切断点色因子境界和（BF §2.2.7）。
方針：削除和を有限同値で隙間へ移し、両端零の隙間の補集合和を使う。
規約：元の非零辺切断の存在も標数条件も外部入力としない。
使われ方：χ の微分保存の切断点部分。 -/
lemma pivotResidualValue_sum_eq_boundary {n d : ℕ} (u : BasisWord n (d + 1)) :
    ∑ c, pivotResidualValue A u c = ∑ p, pivotBoundaryValue A u p := by
  rw [pivotResidualValue_sum, pivotBoundaryValue_sum_subtype]
  congr 1
  exact gap_sum_complement u.val (gapTensor A u)
    (gapTensor_first_positive A u) (gapTensor_last_positive A u)

end SerrePositivity.EInfinity.IntervalCuts

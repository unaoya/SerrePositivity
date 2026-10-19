module

public import SerrePositivity.EInfinity.IntervalCuts.RegularCutEquivalence
public import SerrePositivity.EInfinity.IntervalCuts.CutFactorBoundary
public import SerrePositivity.EInfinity.IntervalCuts.DeletedCutSums

/-!
# 反復色の実際の因子境界と正規化二削除値

概要：Berger–Fresse §2.2.7 の一反復色の因子境界を左右二削除の実際の共通次数の値へ戻す。
方針：端点置換テンソルを境界の指定次数へ移し、両削除係数の公式を適用する。
規約：全て実際の反復テンソルの次数 −d へ置く。
使われ方：元切断非零部分の全削除和と反復色全因子境界和の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：非零切断の指定色の符号付き因子境界を共通次数へ移した値（BF §2.2.7）。
方針：実際の因子境界へ切断符号を掛け、次数等式の射で移す。
規約：出力次数は語次数 d の負。
使われ方：切断点色と全反復色の因子境界を同じ成分で足す。 -/
def factorBoundaryValue {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) (k : Fin n) : (power (interval A) n).X (-(d : ℤ)) :=
  eqToHom (congrArg (fun r : ℤ => (power (interval A) n).X r)
      (by have := edgeOutput_tupleDegree u p h
          omega : -(tupleDegree n (edgeOutput u p) : ℤ) + 1 = -(d : ℤ)))
    (edgeSign u.val p • tensorBoundaryTerm A n (edgeOutput u p) k)

/-- 概要：共通の因子境界値の切断点色は既存の切断点境界値（BF §2.2.7）。
方針：非零判定を解き、同じ実際の因子境界の次数移送を比較する。
規約：語の全次数に成立する。
使われ方：二種類の因子境界和を統合する。 -/
lemma factorBoundaryValue_pivot {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) :
    factorBoundaryValue A u p h (u.val p) = pivotBoundaryValue A u p := by
  rw [pivotBoundaryValue, dite_eq_left h]
  rfl

/-- 概要：左端点置換の次数移送は実際の左削除基底語の指定次数テンソル（BF §2.2.7）。
方針：既存の端点置換の削除語公式と次数等式の射の合成を使う。
規約：元語次数 d+1 の境界次数 −(d+1)。
使われ方：反復色の終点側を正規化削除値へ戻す。 -/
lemma endpointTensor_eraseCut_left_degree {n d : ℕ} (u : BasisWord n (d + 1))
    (p i : Fin (n + (d + 1))) (q : Fin (n + d)) (hq : i.succAbove q = p)
    (h : EdgeNondegenerate u.val p) (hi : i < p)
    (hr : ∃ j, j ≠ i ∧ u.val j = u.val i) :
    let v := eraseCutBasisWord u p i h (ne_of_lt hi) hr
    eqToHom (congrArg (fun r : ℤ => (power (interval A) n).X r)
        (by have := edgeOutput_tupleDegree u p h
            omega : -(tupleDegree n (edgeOutput u p) : ℤ) + 1 = -((d + 1 : ℕ) : ℤ)))
      (endpointTensor A n (edgeOutput u p) (u.val i) (edgeOutput_repeat_color u p h i hr) 1) =
      tensorVectorOfDegree A n (d + 1) (edgeOutput v q)
        (edgeOutput_tupleDegree v q (erase_edgeNondegenerate u.val i q (by rw [hq]; exact h))) := by
  subst p
  dsimp only
  rw [endpointTensor_eraseCut_left A u i q h hi hr]
  simp only [tensorVectorAt, tensorVectorOfDegree, ← ModuleCat.comp_apply, eqToHom_trans]

/-- 概要：右端点置換の次数移送は実際の右削除基底語の指定次数テンソル（BF §2.2.7）。
方針：既存の端点置換の削除語公式と次数等式の射の合成を使う。
規約：元語次数 d+1 の境界次数 −(d+1)。
使われ方：反復色の始点側を正規化削除値へ戻す。 -/
lemma endpointTensor_eraseCut_right_degree {n d : ℕ} (u : BasisWord n (d + 1))
    (p i : Fin (n + (d + 1))) (q : Fin (n + d)) (hq : i.succAbove q = p)
    (h : EdgeNondegenerate u.val p) (hi : p < i)
    (hr : ∃ j, j ≠ i ∧ u.val j = u.val i) :
    let v := eraseCutBasisWord u p i h (ne_of_gt hi) hr
    eqToHom (congrArg (fun r : ℤ => (power (interval A) n).X r)
        (by have := edgeOutput_tupleDegree u p h
            omega : -(tupleDegree n (edgeOutput u p) : ℤ) + 1 = -((d + 1 : ℕ) : ℤ)))
      (endpointTensor A n (edgeOutput u p) (u.val i) (edgeOutput_repeat_color u p h i hr) 0) =
      tensorVectorOfDegree A n (d + 1) (edgeOutput v q)
        (edgeOutput_tupleDegree v q (erase_edgeNondegenerate u.val i q (by rw [hq]; exact h))) := by
  subst p
  dsimp only
  rw [endpointTensor_eraseCut_right A u i q h hi hr]
  simp only [tensorVectorAt, tensorVectorOfDegree, ← ModuleCat.comp_apply, eqToHom_trans]

/-- 概要：一反復色の共通次数の実際の因子境界は左右二削除値の和（BF §2.2.7）。
方針：位置対の二削除位置で因子境界公式を使い、端点値を実際の削除テンソルへ移す。
規約：二削除とも元の非零切断点を残す。
使われ方：元切断非零の全削除和の二項ごとの比較。 -/
lemma RepeatCutPair.factorBoundary_eq_pair {n d : ℕ} (u : BasisWord n (d + 1))
    (c : RepeatCutPair u.val) :
    factorBoundaryValue A u c.pivot c.nondegenerate (u.val c.left) =
      normalizedDeletedValue A u (RepeatCutPair.normalizedCut u c 0).val +
        normalizedDeletedValue A u (RepeatCutPair.normalizedCut u c 1).val := by
  have hq0 : c.left.succAbove (c.erasePosition 0) = c.pivot := c.erasePosition_spec 0
  have hq1 : c.right.succAbove (c.erasePosition 1) = c.pivot := c.erasePosition_spec 1
  have hp : EdgeNondegenerate u.val (c.left.succAbove (c.erasePosition 0)) := by
    rw [hq0]
    exact c.nondegenerate
  have hbase : factorBoundaryValue A u (c.left.succAbove (c.erasePosition 0)) hp
      (u.val c.left) =
        normalizedDeletedValue A u (RepeatCutPair.normalizedCut u c 0).val +
          normalizedDeletedValue A u (RepeatCutPair.normalizedCut u c 1).val := by
    have h := cut_factor_boundary A u c.left c.right (c.erasePosition 0) (c.erasePosition 1)
      (hq1.trans hq0.symm) hp c.ordered c.same_color
    dsimp only at h
    unfold factorBoundaryValue
    rw [h]
    simp only [map_add, map_zsmul]
    have hL := endpointTensor_eraseCut_left_degree A u _ c.left (c.erasePosition 0) rfl hp
      (by rw [hq0]; exact c.straddles.1) ⟨c.right, ne_of_gt c.ordered, c.same_color.symm⟩
    have hR := endpointTensor_eraseCut_right_degree A u _ c.right (c.erasePosition 1)
      (hq1.trans hq0.symm) hp (by rw [hq0]; exact c.straddles.2)
      ⟨c.left, ne_of_lt c.ordered, c.same_color⟩
    dsimp only at hL hR
    rw [hL]
    have hc : u.val c.right = u.val c.left := c.same_color.symm
    simp only [hc] at hR
    rw [hR]
    rfl
  simpa only [hq0] using! hbase

end SerrePositivity.EInfinity.IntervalCuts

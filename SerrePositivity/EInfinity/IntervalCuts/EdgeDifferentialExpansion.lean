module

public import SerrePositivity.EInfinity.IntervalCuts.DeletedCutFibers
public import SerrePositivity.EInfinity.IntervalCuts.EdgeGeneratorCutSum
public import SerrePositivity.EInfinity.IntervalCuts.DeletedCutSums
public import SerrePositivity.EInfinity.Surjection.DeletionDifferential

/-!
# 実際の削除微分の辺成分と正規化全削除和

概要：Berger–Fresse §1.2.3 の削除微分を実際の区間テンソルに送ると共通添字の全和になる。
方針：非全射・退化生成元を含む辺成分公式を各削除に適用し、依存組の有限和へ移す。
規約：整数の削除係数と切断符号を同じ実際のテンソル成分で掛け合わせる。
使われ方：辺成分の微分保存を元切断非零部分の境界比較へ帰着する。
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

/-- 概要：削除微分の実際の辺成分は正規化削除切断の全符号付き値（BF §1.2.3・§2.2.7）。
方針：各生成元の辺成分を展開し、全射削除位置と非零切断の依存組へ添字替えする。
規約：非全射・退化削除の零項も元の微分には含まれる。
使われ方：正規化全削除和の三部分比較を実際の微分へ接続する。 -/
lemma edgeComponent_differentialOnWord {n d : ℕ} (u : BasisWord n (d + 1)) :
    edgeComponent A n d (differentialOnWord A u) = ∑ c, normalizedDeletedValue A u c := by
  classical
  rw [NormalizedDeletedCut.sum_fibers]
  simp only [differentialOnWord, map_sum, map_zsmul, edgeComponent_generator]
  calc
    _ = ∑ i : Fin (n + (d + 1)),
        if hs : Function.Surjective (erase u.val i) then
          ∑ q : {q : Fin (n + d) // EdgeNondegenerate (erase u.val i) q},
            normalizedDeletedValue A u ⟨i, q.val, hs, q.property⟩
        else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hs : Function.Surjective (erase u.val i)
      · simp only [dite_eq_left hs]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro q _
        simp only [smul_smul, normalizedDeletedValue, NormalizedDeletedCut.word]
      · simp only [dite_eq_right hs, smul_zero]
    _ = _ := by
      rw [sum_dite_eq_subtype]
      rfl

/-- 概要：削除微分の実際の辺成分は元切断非零部分と切断点色の全境界和（BF §2.2.7）。
方針：実際の微分展開に三部分の全処理を適用する。
規約：二種類の障害項を仮定として残さない。
使われ方：反復色因子の境界比較だけを残す。 -/
lemma edgeComponent_differentialOnWord_reduce {n d : ℕ} (u : BasisWord n (d + 1)) :
    edgeComponent A n d (differentialOnWord A u) =
      (∑ c : NormalizedDeletedCut.Regular u.val, normalizedDeletedValue A u c.val) +
        ∑ p, pivotBoundaryValue A u p := by
  rw [edgeComponent_differentialOnWord, normalizedDeletedValue_sum_reduce]

/-- 概要：元の非零切断がなければ実際の削除微分の辺成分も零（BF §2.2.7）。
方針：正規化全削除和への展開とその全相殺を使う。
規約：元の辺成分が零となる語の実際の微分値を計算する。
使われ方：全微分保存の退化元切断の分岐。 -/
lemma edgeComponent_differentialOnWord_eq_zero_of_no_cut {n d : ℕ}
    (u : BasisWord n (d + 1)) (h : ∀ p, ¬ EdgeNondegenerate u.val p) :
    edgeComponent A n d (differentialOnWord A u) = 0 := by
  rw [edgeComponent_differentialOnWord, normalizedDeletedValue_sum_eq_zero_of_no_cut A u h]

end SerrePositivity.EInfinity.IntervalCuts

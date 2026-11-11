module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWDifferential
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearResidual

/-!
# 標準削除境界の全域的な和

概要：空集合の評価を零に延長して、全ての削除点を同じ境界和に含める。
方針：二点以上では既存の評価と比較し、一点以下では削除後が空であることを使う。
規約：標準境界の符号は昇順の点数による。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW 境界の二重和の相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：標準境界は空集合の値を零とした全ての点の削除和に等しい。
方針：濃度二以上では各成分を戻し、濃度一以下では全削除集合を空とする。
規約：空集合や一点集合も別の式を要求せず扱う。
使われ方：Kerodon 2.5.8（Tag 00S0） の左右の境界和を統一する式。 -/
lemma standardRhs_eq_deleteSum {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs f J k hk = ∑ j : J, (-1 : ℤ) ^ (J.filter (· < j.val)).card •
      f.componentOrZero (J.erase j.val) (k + 1) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs
  split_ifs with hJ
  · apply Finset.sum_congr rfl
    intro j _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq f _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ j.val j.property)
      (by have := Finset.card_erase_add_one j.property; omega)]
  · symm
    apply Finset.sum_eq_zero
    intro j _
    have he : J.erase j.val = ∅ := by
      apply Finset.card_eq_zero.mp
      have := Finset.card_erase_add_one j.property
      omega
    rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_empty, smul_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

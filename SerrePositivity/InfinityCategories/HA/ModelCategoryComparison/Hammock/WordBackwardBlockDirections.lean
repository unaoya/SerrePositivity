module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WordBackwardBlocks

/-!
# 切り出した局所語の全列の向きの回収

概要：三つの backward 列と間の forward 列の全ての向きを元の語と照合する。
方針：元の局所形の全列の場合分けと、最も近い境界列の性質を使う。
規約：元の列番号を保持する。長さ零でも同じ場合分けを使う。
使われ方：元の全体の語の厳密な prefix/core/suffix 分解。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward

variable {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {p : Fin w.length} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardBounds w p)

lemma core_direction (i : Fin h.coreWord.length) :
    h.coreWord.direction i = w.direction (h.coreIndex i) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.column_cases h.leftLength h.rightLength
    (P := fun i => h.coreWord.direction i = w.direction (h.coreIndex i))
  · rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.first_direction, h.firstIndex, h.left_backward]
  · intro j
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.left_direction]
    apply Eq.symm (h.left_forward _ ?_ ?_)
    all_goals
      have hi := j.isLt
      have hl := h.left_lt
      simp only [Fin.lt_def, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreIndex_val, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftColumn_val]
      dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.leftLength] at hi
      omega
  · rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middle_direction, h.middleIndex, h.middle_backward]
  · intro j
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.right_direction]
    apply Eq.symm (h.right_forward _ ?_ ?_)
    all_goals
      have hi := j.isLt
      have hl := h.left_lt
      have hr := h.lt_right
      simp only [Fin.lt_def, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreIndex_val, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightColumn_val]
      dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.leftLength, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.rightLength] at hi ⊢
      omega
  · rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.last_direction, h.lastIndex, h.right_backward]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardBounds
  export _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds (core_direction)

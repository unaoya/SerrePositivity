module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WordBackwardBlockDirections

/-!
# 指定 backward 列を保つ元の語の厳密な局所分解

概要：切り出した前後の語と局所語を連結すると、元の語そのものに等しい。
方針：元の全列の方向と番号を照合し、中央列の位置も回収する。
規約：語の同型類だけで済ませず、元の列を保持する等式を証明する。
使われ方：既存の局所挿入の弱同値性を元の指定列へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward

variable {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {p : Fin w.length} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardBounds w p)

lemma whole_eq : h.wholeWord = w := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext _ _ h.whole_length
  intro i
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.addCases with
    | left i =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left]
      apply congrArg w.direction
      apply Fin.ext
      rfl
    | right i =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right, h.core_direction]
      apply congrArg w.direction
      apply Fin.ext
      rfl
  | right i =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right]
    apply congrArg w.direction
    apply Fin.ext
    change h.right.val + 1 + i.val = h.left.val + h.coreWord.length + i.val
    have hlen := h.core_length
    have hl := h.left_lt
    have hr := h.lt_right
    omega

lemma middle_column_cast :
    Fin.cast h.whole_length
      (((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn h.leftLength h.rightLength).natAdd h.prefixWord.length).castAdd
        h.suffixWord.length) = p := by
  apply Fin.ext
  change h.left.val + (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn h.leftLength h.rightLength).val = p.val
  exact congrArg Fin.val h.middleIndex

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardBounds
  export _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds (whole_eq middle_column_cast)

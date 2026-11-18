module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordBackwardBounds
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackwardPositionCases

/-!
# 元の両隣の backward 列から左右の区間長と前後の語を切り出す

概要：指定中央列と両隣の backward 列の番号から、元の局所形の長さを構成する。
方針：元の列番号の区間をそのまま使い、前後の任意の向きも保持する。
規約：左右の forward 区間の長さ零を許す。
使われ方：任意の padded な語を既存の中央列の比較へ戻す。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward

variable {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {p : Fin w.length} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardBounds w p)

abbrev leftLength : ℕ := p.val - h.left.val - 1
abbrev rightLength : ℕ := h.right.val - p.val - 1

def prefixWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word where
  length := h.left.val
  direction i := w.direction ⟨i.val, lt_trans i.isLt h.left.isLt⟩

def suffixWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word where
  length := w.length - h.right.val - 1
  direction i := w.direction ⟨h.right.val + 1 + i.val, by
    have hi := i.isLt
    have hr := h.right.isLt
    omega⟩

abbrev coreWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.leftLength h) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.rightLength h)

lemma core_length : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreWord h).length = h.right.val - h.left.val + 1 := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.length_eq]
  have hl := h.left_lt
  have hr := h.lt_right
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.leftLength, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.rightLength]
  omega

def coreIndex (i : Fin (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreWord h).length) : Fin w.length :=
  ⟨h.left.val + i.val, by
    have hi := i.isLt
    have hlen := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.core_length h)
    have hl := h.left_lt
    have hr := h.lt_right
    have hlast := h.right.isLt
    omega⟩

lemma coreIndex_val (i : Fin (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreWord h).length) : ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreIndex h i)).val = h.left.val + i.val := rfl

lemma firstIndex : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreIndex h (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.firstColumn (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.leftLength h) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.rightLength h))) = h.left :=
  Fin.ext (by rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreIndex_val, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.firstColumn_val]; omega)

lemma middleIndex : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreIndex h (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.leftLength h) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.rightLength h))) = p := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreIndex_val, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn_val]
  have hl := h.left_lt
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.leftLength]
  omega

lemma lastIndex : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreIndex h (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.lastColumn (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.leftLength h) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.rightLength h))) = h.right := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreIndex_val, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.lastColumn_val]
  have hl := h.left_lt
  have hr := h.lt_right
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.leftLength, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.rightLength]
  omega

abbrev wholeWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.prefixWord h) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreWord h)) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.suffixWord h)

lemma whole_length : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.wholeWord h).length = w.length := by
  change h.left.val + (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.coreWord h).length + (w.length - h.right.val - 1) = _
  rw [(_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds.core_length h)]
  have hl := h.left_lt
  have hr := h.lt_right
  have hlast := h.right.isLt
  omega

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardBounds
  export _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Word.BackwardBounds
    (leftLength rightLength prefixWord suffixWord coreWord core_length coreIndex coreIndex_val
      firstIndex middleIndex lastIndex wholeWord whole_length)

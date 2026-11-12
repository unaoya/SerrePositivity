module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordBackwardBounds
public import SerrePositivity.EInfinity.Hammock.MiddleBackwardPositionCases

/-!
# 元の両隣の backward 列から左右の区間長と前後の語を切り出す

概要：指定中央列と両隣の backward 列の番号から、元の局所形の長さを構成する。
方針：元の列番号の区間をそのまま使い、前後の任意の向きも保持する。
規約：左右の forward 区間の長さ零を許す。
使われ方：任意の padded な語を既存の中央列の比較へ戻す。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Word.BackwardBounds
open MiddleBackward

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

abbrev coreWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word (leftLength h) (rightLength h)

lemma core_length : (coreWord h).length = h.right.val - h.left.val + 1 := by
  rw [Positions.length_eq]
  have hl := h.left_lt
  have hr := h.lt_right
  dsimp only [leftLength, rightLength]
  omega

def coreIndex (i : Fin (coreWord h).length) : Fin w.length :=
  ⟨h.left.val + i.val, by
    have hi := i.isLt
    have hlen := (core_length h)
    have hl := h.left_lt
    have hr := h.lt_right
    have hlast := h.right.isLt
    omega⟩

lemma coreIndex_val (i : Fin (coreWord h).length) : ((coreIndex h i)).val = h.left.val + i.val := rfl

lemma firstIndex : (coreIndex h (Positions.firstColumn (leftLength h) (rightLength h))) = h.left :=
  Fin.ext (by rw [coreIndex_val, Positions.firstColumn_val]; omega)

lemma middleIndex : (coreIndex h (Positions.middleColumn (leftLength h) (rightLength h))) = p := by
  apply Fin.ext
  rw [coreIndex_val, Positions.middleColumn_val]
  have hl := h.left_lt
  dsimp only [leftLength]
  omega

lemma lastIndex : (coreIndex h (Positions.lastColumn (leftLength h) (rightLength h))) = h.right := by
  apply Fin.ext
  rw [coreIndex_val, Positions.lastColumn_val]
  have hl := h.left_lt
  have hr := h.lt_right
  dsimp only [leftLength, rightLength]
  omega

abbrev wholeWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (prefixWord h) (coreWord h)) (suffixWord h)

lemma whole_length : (wholeWord h).length = w.length := by
  change h.left.val + (coreWord h).length + (w.length - h.right.val - 1) = _
  rw [(core_length h)]
  have hl := h.left_lt
  have hr := h.lt_right
  have hlast := h.right.isLt
  omega

end SerrePositivity.EInfinity.Hammock.Word.BackwardBounds

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardBounds
  export _root_.SerrePositivity.EInfinity.Hammock.Word.BackwardBounds
    (leftLength rightLength prefixWord suffixWord coreWord core_length coreIndex coreIndex_val
      firstIndex middleIndex lastIndex wholeWord whole_length)

module

public import SerrePositivity.EInfinity.Hammock.WordBackwardBounds
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

variable {w : Word} {p : Fin w.length} (h : BackwardBounds w p)

abbrev leftLength : ℕ := p.val - h.left.val - 1
abbrev rightLength : ℕ := h.right.val - p.val - 1

def prefixWord : Word where
  length := h.left.val
  direction i := w.direction ⟨i.val, lt_trans i.isLt h.left.isLt⟩

def suffixWord : Word where
  length := w.length - h.right.val - 1
  direction i := w.direction ⟨h.right.val + 1 + i.val, by
    have hi := i.isLt
    have hr := h.right.isLt
    omega⟩

abbrev coreWord : Word := word h.leftLength h.rightLength

lemma core_length : h.coreWord.length = h.right.val - h.left.val + 1 := by
  rw [Positions.length_eq]
  have hl := h.left_lt
  have hr := h.lt_right
  dsimp only [leftLength, rightLength]
  omega

def coreIndex (i : Fin h.coreWord.length) : Fin w.length :=
  ⟨h.left.val + i.val, by
    have hi := i.isLt
    have hlen := h.core_length
    have hl := h.left_lt
    have hr := h.lt_right
    have hlast := h.right.isLt
    omega⟩

lemma coreIndex_val (i : Fin h.coreWord.length) : (h.coreIndex i).val = h.left.val + i.val := rfl

lemma firstIndex : h.coreIndex (Positions.firstColumn h.leftLength h.rightLength) = h.left :=
  Fin.ext (by rw [coreIndex_val, Positions.firstColumn_val]; omega)

lemma middleIndex : h.coreIndex (Positions.middleColumn h.leftLength h.rightLength) = p := by
  apply Fin.ext
  rw [coreIndex_val, Positions.middleColumn_val]
  have hl := h.left_lt
  dsimp only [leftLength]
  omega

lemma lastIndex : h.coreIndex (Positions.lastColumn h.leftLength h.rightLength) = h.right := by
  apply Fin.ext
  rw [coreIndex_val, Positions.lastColumn_val]
  have hl := h.left_lt
  have hr := h.lt_right
  dsimp only [leftLength, rightLength]
  omega

abbrev wholeWord : Word := append (append h.prefixWord h.coreWord) h.suffixWord

lemma whole_length : h.wholeWord.length = w.length := by
  change h.left.val + h.coreWord.length + (w.length - h.right.val - 1) = _
  rw [h.core_length]
  have hl := h.left_lt
  have hr := h.lt_right
  have hlast := h.right.isLt
  omega

end SerrePositivity.EInfinity.Hammock.Word.BackwardBounds

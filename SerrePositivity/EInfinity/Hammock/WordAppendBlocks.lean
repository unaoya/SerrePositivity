module

public import SerrePositivity.EInfinity.Hammock.WordBlock
public import SerrePositivity.EInfinity.Hammock.WordAppendIntervals

/-!
# 連結語の元の左右の連続部分

概要：元の二つの語を、連結語の具体的な連続部分として構成する。
方針：左は零、右は元の左語の長さだけ列番号と頂点番号をずらす。
規約：向きの保存と番号の式を元の語から証明する。
使われ方：区間合成の連続部分比較を、実際の連結へ代入する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word

def leftBlock (a b : Word) : Block a (append a b) where
  offset := 0
  bound := by change 0 + a.length ≤ a.length + b.length; omega
  direction_eq i := by
    have h : (⟨0 + i.val, by have := i.isLt; dsimp [append]; omega⟩ : Fin (append a b).length) =
        i.castAdd b.length := Fin.ext (Nat.zero_add _)
    exact (congrArg (append a b).direction h).trans (append_direction_left a b i)

def rightBlock (a b : Word) : Block b (append a b) where
  offset := a.length
  bound := le_rfl
  direction_eq i := append_direction_right a b i

lemma leftBlock_vertex (a b : Word) (j : Fin (a.length + 1)) :
    (leftBlock a b).vertex j = leftVertex a b j := Fin.ext (Nat.zero_add _)

lemma leftBlock_column (a b : Word) (i : Fin a.length) :
    (leftBlock a b).column i = i.castAdd b.length := Fin.ext (Nat.zero_add _)

lemma rightBlock_vertex (a b : Word) (j : Fin (b.length + 1)) :
    (rightBlock a b).vertex j = rightVertex a b j := rfl

lemma rightBlock_column (a b : Word) (i : Fin b.length) :
    (rightBlock a b).column i = i.natAdd a.length := rfl

end SerrePositivity.EInfinity.Hammock.Word

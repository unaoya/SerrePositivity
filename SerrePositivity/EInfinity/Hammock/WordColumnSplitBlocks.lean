module

public import SerrePositivity.EInfinity.Hammock.WordColumnSplitVertices
public import SerrePositivity.EInfinity.Hammock.WordBlock

/-!
# 元の任意列の前後の語の連続部分の包含

概要：前後の切断語を、元の同じ語の連続部分として構成する。
方針：前は offset 零、後は指定列の次の番号を使う。
規約：空の前後の語と元の全方向を保持する。
使われ方：切り出した区間合成の元の語への回収。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.Hammock.Word.ColumnSplit

variable (w : Word) (p : Fin w.length)

def beforeBlock : Block (before w p) w where
  offset := 0
  bound := by
    have hp := p.isLt
    change 0 + p.val ≤ w.length
    omega
  direction_eq j := by
    apply congrArg w.direction
    apply Fin.ext
    change 0 + j.val = j.val
    omega

def afterBlock : Block (after w p) w where
  offset := p.val + 1
  bound := by
    have hp := p.isLt
    change p.val + 1 + (w.length - p.val - 1) ≤ w.length
    omega
  direction_eq _ := rfl

lemma beforeBlock_vertex (k : Fin ((before w p).length + 1)) :
    (beforeBlock w p).vertex k = beforeVertex w p k := by
  apply Fin.ext
  change 0 + k.val = k.val
  omega

lemma afterBlock_vertex (k : Fin ((after w p).length + 1)) :
    (afterBlock w p).vertex k = afterVertex w p k := Fin.ext rfl

end SerrePositivity.EInfinity.Hammock.Word.ColumnSplit

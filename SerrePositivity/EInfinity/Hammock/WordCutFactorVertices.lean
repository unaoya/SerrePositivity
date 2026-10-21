module

public import SerrePositivity.EInfinity.Hammock.WordCutFactorColumns
public import SerrePositivity.EInfinity.Hammock.WordAppendIndices

/-!
# 切断因子の前後の元の頂点番号

概要：prefix の前の語と残りの後の語の頂点を元の同じ語へ戻す。
方針：prefix は同じ番号、残りは切断列の次からの番号を使う。
規約：端点と空の前後の語を含む。
使われ方：制限した語の射の元の cut の照合。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.Hammock.Word.CutFactor

variable (w : Word) (i : Fin w.length)

def prefixVertex (k : Fin ((ColumnSplit.before w i).length + 1)) : Fin (w.length + 1) :=
  ⟨k.val, by
    have hk := k.isLt
    have hi := i.isLt
    change k.val < i.val + 1 at hk
    omega⟩

def residualVertex (k : Fin ((ColumnSplit.after w i).length + 1)) : Fin (w.length + 1) :=
  ⟨i.val + 1 + k.val, by
    have hk := k.isLt
    have hi := i.isLt
    change k.val < w.length - i.val - 1 + 1 at hk
    omega⟩

lemma prefixVertex_last : prefixVertex w i (Fin.last (ColumnSplit.before w i).length) =
    i.castSucc := by apply Fin.ext; rfl

lemma residualVertex_zero : residualVertex w i 0 = i.succ := by apply Fin.ext; rfl

end SerrePositivity.EInfinity.Hammock.Word.CutFactor

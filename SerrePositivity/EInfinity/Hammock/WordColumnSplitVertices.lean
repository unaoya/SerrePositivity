module

public import SerrePositivity.EInfinity.Hammock.WordColumnSplit

/-!
# 任意列の切断の元の頂点と接合点

概要：前・中央・後の全頂点と二つの接合点を、元の語の同じ頂点へ戻す。
方針：元の有限順序の番号を保持し、連結の頂点埋め込みと照合する。
規約：前後の長さ零と最初・最後の列を含む。
使われ方：切り出した図式の動く端点を元の列の両端に照合する。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.Hammock.Word.ColumnSplit

variable (w : Word) (p : Fin w.length)

def beforeVertex (j : Fin ((before w p).length + 1)) : Fin (w.length + 1) :=
  ⟨j.val, by
    have hj := j.isLt
    have hp := p.isLt
    change j.val < p.val + 1 at hj
    omega⟩

def middleVertex (j : Fin ((middle w p).length + 1)) : Fin (w.length + 1) :=
  ⟨p.val + j.val, by
    have hj := j.isLt
    have hp := p.isLt
    change j.val < 2 at hj
    omega⟩

def afterVertex (j : Fin ((after w p).length + 1)) : Fin (w.length + 1) :=
  ⟨p.val + 1 + j.val, by
    have hj := j.isLt
    have hp := p.isLt
    change j.val < w.length - p.val - 1 + 1 at hj
    omega⟩

lemma before_vertex_cast (j : Fin ((before w p).length + 1)) :
    Fin.cast (congrArg (fun n => n + 1) (whole_length w p))
      (leftVertex (append (before w p) (middle w p)) (after w p)
        (leftVertex (before w p) (middle w p) j)) = beforeVertex w p j := by
  apply Fin.ext
  rfl

lemma middle_vertex_cast (j : Fin ((middle w p).length + 1)) :
    Fin.cast (congrArg (fun n => n + 1) (whole_length w p))
      (leftVertex (append (before w p) (middle w p)) (after w p)
        (rightVertex (before w p) (middle w p) j)) = middleVertex w p j := by
  apply Fin.ext
  rfl

lemma after_vertex_cast (j : Fin ((after w p).length + 1)) :
    Fin.cast (congrArg (fun n => n + 1) (whole_length w p))
      (rightVertex (append (before w p) (middle w p)) (after w p) j) =
        afterVertex w p j := by
  apply Fin.ext
  rfl

lemma middleVertex_zero : middleVertex w p 0 = p.castSucc := by apply Fin.ext; rfl

lemma middleVertex_last : middleVertex w p (Fin.last 1) = p.succ := by apply Fin.ext; rfl

lemma beforeVertex_last : beforeVertex w p (Fin.last (before w p).length) = p.castSucc := by
  apply Fin.ext
  rfl

lemma afterVertex_zero : afterVertex w p 0 = p.succ := by apply Fin.ext; rfl

lemma middle_forward (h : w.direction p = .forward) : middle w p = single .forward :=
  congrArg single h

end SerrePositivity.EInfinity.Hammock.Word.ColumnSplit

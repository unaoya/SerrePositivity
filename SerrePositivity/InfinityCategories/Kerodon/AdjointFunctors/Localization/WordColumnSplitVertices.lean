module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit

/-!
# 任意列の切断の元の頂点と接合点

概要：前・中央・後の全頂点と二つの接合点を、元の語の同じ頂点へ戻す。
方針：元の有限順序の番号を保持し、連結の頂点埋め込みと照合する。
規約：前後の長さ零と最初・最後の列を含む。
使われ方：切り出した図式の動く端点を元の列の両端に照合する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

variable (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length)

def beforeVertex (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length + 1)) : Fin (w.length + 1) :=
  ⟨j.val, by
    have hj := j.isLt
    have hp := p.isLt
    change j.val < p.val + 1 at hj
    omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.beforeVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (beforeVertex)


def middleVertex (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p).length + 1)) : Fin (w.length + 1) :=
  ⟨p.val + j.val, by
    have hj := j.isLt
    have hp := p.isLt
    change j.val < 2 at hj
    omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.middleVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (middleVertex)


def afterVertex (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p).length + 1)) : Fin (w.length + 1) :=
  ⟨p.val + 1 + j.val, by
    have hj := j.isLt
    have hp := p.isLt
    change j.val < w.length - p.val - 1 + 1 at hj
    omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.afterVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (afterVertex)


lemma before_vertex_cast (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length + 1)) :
    Fin.cast (congrArg (fun n => n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_length w p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p) j)) = beforeVertex w p j := by
  apply Fin.ext
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.before_vertex_cast export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (before_vertex_cast)


lemma middle_vertex_cast (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p).length + 1)) :
    Fin.cast (congrArg (fun n => n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_length w p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p) j)) = middleVertex w p j := by
  apply Fin.ext
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.middle_vertex_cast export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (middle_vertex_cast)


lemma after_vertex_cast (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p).length + 1)) :
    Fin.cast (congrArg (fun n => n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_length w p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p) j) =
        afterVertex w p j := by
  apply Fin.ext
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.after_vertex_cast export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (after_vertex_cast)


lemma middleVertex_zero : middleVertex w p 0 = p.castSucc := by apply Fin.ext; rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.middleVertex_zero export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (middleVertex_zero)


lemma middleVertex_last : middleVertex w p (Fin.last 1) = p.succ := by apply Fin.ext; rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.middleVertex_last export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (middleVertex_last)


lemma beforeVertex_last : beforeVertex w p (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length) = p.castSucc := by
  apply Fin.ext
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.beforeVertex_last export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (beforeVertex_last)


lemma afterVertex_zero : afterVertex w p 0 = p.succ := by apply Fin.ext; rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.afterVertex_zero export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (afterVertex_zero)


lemma middle_forward (h : w.direction p = .forward) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward :=
  congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.middle_forward export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (middle_forward)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

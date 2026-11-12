module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplitVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordBlock

/-!
# 元の任意列の前後の語の連続部分の包含

概要：前後の切断語を、元の同じ語の連続部分として構成する。
方針：前は offset 零、後は指定列の次の番号を使う。
規約：空の前後の語と元の全方向を保持する。
使われ方：切り出した区間合成の元の語への回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

variable (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length)

def beforeBlock : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Block (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p) w where
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.beforeBlock export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (beforeBlock)


def afterBlock : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Block (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p) w where
  offset := p.val + 1
  bound := by
    have hp := p.isLt
    change p.val + 1 + (w.length - p.val - 1) ≤ w.length
    omega
  direction_eq _ := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.afterBlock export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (afterBlock)


lemma beforeBlock_vertex (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length + 1)) :
    (beforeBlock w p).vertex k = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeVertex w p k := by
  apply Fin.ext
  change 0 + k.val = k.val
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.beforeBlock_vertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (beforeBlock_vertex)


lemma afterBlock_vertex (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p).length + 1)) :
    (afterBlock w p).vertex k = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterVertex w p k := Fin.ext rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.afterBlock_vertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (afterBlock_vertex)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

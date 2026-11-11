module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorColumns
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendIndices

/-!
# 切断因子の前後の元の頂点番号

概要：prefix の前の語と残りの後の語の頂点を元の同じ語へ戻す。
方針：prefix は同じ番号、残りは切断列の次からの番号を使う。
規約：端点と空の前後の語を含む。
使われ方：制限した語の射の元の cut の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

variable (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length)

def prefixVertex (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i).length + 1)) : Fin (w.length + 1) :=
  ⟨k.val, by
    have hk := k.isLt
    have hi := i.isLt
    change k.val < i.val + 1 at hk
    omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixVertex)


def residualVertex (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i).length + 1)) : Fin (w.length + 1) :=
  ⟨i.val + 1 + k.val, by
    have hk := k.isLt
    have hi := i.isLt
    change k.val < w.length - i.val - 1 + 1 at hk
    omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualVertex)


lemma prefixVertex_last : prefixVertex w i (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i).length) =
    i.castSucc := by apply Fin.ext; rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixVertex_last export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixVertex_last)


lemma residualVertex_zero : residualVertex w i 0 = i.succ := by apply Fin.ext; rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualVertex_zero export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualVertex_zero)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

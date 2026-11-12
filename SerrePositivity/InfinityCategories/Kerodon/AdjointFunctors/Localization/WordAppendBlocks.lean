module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordBlock
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendIntervals

/-!
# 連結語の元の左右の連続部分

概要：元の二つの語を、連結語の具体的な連続部分として構成する。
方針：左は零、右は元の左語の長さだけ列番号と頂点番号をずらす。
規約：向きの保存と番号の式を元の語から証明する。
使われ方：区間合成の連続部分比較を、実際の連結へ代入する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks

def leftBlock (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Block a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) where
  offset := 0
  bound := by change 0 + a.length ≤ a.length + b.length; omega
  direction_eq i := by
    have h : (⟨0 + i.val, by have := i.isLt; dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append]; omega⟩ : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length) =
        i.castAdd b.length := Fin.ext (Nat.zero_add _)
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).direction h).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a b i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks (leftBlock)


def rightBlock (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Block b (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) where
  offset := a.length
  bound := le_rfl
  direction_eq i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a b i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks (rightBlock)


lemma leftBlock_vertex (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j : Fin (a.length + 1)) :
    (leftBlock a b).vertex j = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b j := Fin.ext (Nat.zero_add _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks (leftBlock_vertex)


lemma leftBlock_column (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin a.length) :
    (leftBlock a b).column i = i.castAdd b.length := Fin.ext (Nat.zero_add _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks (leftBlock_column)


lemma rightBlock_vertex (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j : Fin (b.length + 1)) :
    (rightBlock a b).vertex j = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b j := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks (rightBlock_vertex)


lemma rightBlock_column (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin b.length) :
    (rightBlock a b).column i = i.natAdd a.length := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks (rightBlock_column)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks

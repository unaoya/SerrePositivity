module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit

/-!
# 内部切断の prefix・残りの語と元の列番号

概要：切断列の内部の前後の一列を含む語の全列を、元の同じ列番号へ照合する。
方針：prefix は零から切断列まで、残りは切断列から最後までの番号を使う。
規約：切断列は forward、前後の空語も含む。
使われ方：元の語の射を切断因子の語へ制限する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

abbrev prefixWord (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixWord export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixWord)


abbrev residualWord (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualWord export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualWord)


def prefixColumn (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) (k : Fin (prefixWord w i).length) :
    Fin w.length := ⟨k.val, by
      have hk := k.isLt
      have hi := i.isLt
      change k.val < i.val + 1 at hk
      omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixColumn export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixColumn)


def residualColumn (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) (k : Fin (residualWord w i).length) :
    Fin w.length := ⟨i.val + k.val, by
      have hk := k.isLt
      have hi := i.isLt
      change k.val < 1 + (w.length - i.val - 1) at hk
      omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualColumn export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualColumn)


lemma prefixColumn_le (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) (k : Fin (prefixWord w i).length) :
    prefixColumn w i k ≤ i := by
  have hk := k.isLt
  change k.val < i.val + 1 at hk
  exact Nat.le_of_lt_succ hk

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixColumn_le export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixColumn_le)


lemma le_residualColumn (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) (k : Fin (residualWord w i).length) :
    i ≤ residualColumn w i k := by change i.val ≤ i.val + k.val; omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.le_residualColumn export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (le_residualColumn)


lemma prefix_direction (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) (hi : w.direction i = .forward)
    (k : Fin (prefixWord w i).length) :
    (prefixWord w i).direction k = w.direction (prefixColumn w i k) := by
  cases k using Fin.addCases with
  | left k =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left]
    rfl
  | right k =>
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right]
    exact hi.symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefix_direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefix_direction)


lemma residual_direction (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) (hi : w.direction i = .forward)
    (k : Fin (residualWord w i).length) :
    (residualWord w i).direction k = w.direction (residualColumn w i k) := by
  cases k using Fin.addCases with
  | left k =>
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left]
    exact hi.symm
  | right k =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right]
    apply congrArg w.direction
    apply Fin.ext
    change i.val + 1 + k.val = i.val + (1 + k.val)
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residual_direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residual_direction)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

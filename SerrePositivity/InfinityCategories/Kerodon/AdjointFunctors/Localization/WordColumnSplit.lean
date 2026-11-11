module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendIndices

/-!
# 元の任意の一列を保つ語の切断

概要：任意の列の前後の語を切り出し、同じ一列を挟む連結で元の語を回収する。
方針：元の列番号の前後を有限順序で制限し、全方向を照合する。
規約：向きは任意。端の列と空の前後の語を含む。
使われ方：非指定生成矢を持つ forward 列の前後の全語の抽出。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit

variable (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length)

def before : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word where
  length := p.val
  direction j := w.direction ⟨j.val, lt_trans j.isLt p.isLt⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.before export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit (before)


def after : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word where
  length := w.length - p.val - 1
  direction j := w.direction ⟨p.val + 1 + j.val, by have := j.isLt; have := p.isLt; omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.after export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit (after)


abbrev middle : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single (w.direction p)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.middle export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit (middle)

abbrev whole : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (before w p) (middle w p)) (after w p)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.whole export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit (whole)


lemma whole_length : (whole w p).length = w.length := by
  change p.val + 1 + (w.length - p.val - 1) = w.length
  have := p.isLt
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.whole_length export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit (whole_length)


lemma whole_eq : whole w p = w := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext _ _ (whole_length w p)
  intro j
  cases j using Fin.addCases with
  | left j =>
    cases j using Fin.addCases with
    | left j =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left]
      apply congrArg w.direction
      apply Fin.ext
      rfl
    | right j =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right]
      change w.direction p = w.direction _
      apply congrArg w.direction
      apply Fin.ext
      have hj : j.val < 1 := j.isLt
      change p.val = p.val + j.val
      omega
  | right j =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right]
    apply congrArg w.direction
    apply Fin.ext
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.whole_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit (whole_eq)


lemma middle_column_cast :
    Fin.cast (whole_length w p)
      (((0 : Fin 1).natAdd (before w p).length).castAdd (after w p).length) = p := by
  apply Fin.ext
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.middle_column_cast export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit (middle_column_cast)


lemma before_first_empty (p : Fin w.length) (h : p.val = 0) : before w p = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext _ _ h
  intro j
  have := j.isLt
  change j.val < p.val at this
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.before_first_empty export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit (before_first_empty)


lemma after_last_empty (p : Fin w.length) (h : p.val + 1 = w.length) : after w p = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty := by
  have hl : (after w p).length = 0 := by change w.length - p.val - 1 = 0; omega
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext _ _ hl
  intro j
  have := j.isLt
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ColumnSplit.after_last_empty export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit (after_last_empty)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit

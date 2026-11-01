module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordUnit
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordAppendIndices

/-!
# 元の任意の一列を保つ語の切断

概要：任意の列の前後の語を切り出し、同じ一列を挟む連結で元の語を回収する。
方針：元の列番号の前後を有限順序で制限し、全方向を照合する。
規約：向きは任意。端の列と空の前後の語を含む。
使われ方：非指定生成矢を持つ forward 列の前後の全語の抽出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word.ColumnSplit

variable (w : Word) (p : Fin w.length)

def before : Word where
  length := p.val
  direction j := w.direction ⟨j.val, lt_trans j.isLt p.isLt⟩

def after : Word where
  length := w.length - p.val - 1
  direction j := w.direction ⟨p.val + 1 + j.val, by have := j.isLt; have := p.isLt; omega⟩

abbrev middle : Word := single (w.direction p)
abbrev whole : Word := append (append (before w p) (middle w p)) (after w p)

lemma whole_length : (whole w p).length = w.length := by
  change p.val + 1 + (w.length - p.val - 1) = w.length
  have := p.isLt
  omega

lemma whole_eq : whole w p = w := by
  apply object_ext _ _ (whole_length w p)
  intro j
  cases j using Fin.addCases with
  | left j =>
    cases j using Fin.addCases with
    | left j =>
      rw [append_direction_left, append_direction_left]
      apply congrArg w.direction
      apply Fin.ext
      rfl
    | right j =>
      rw [append_direction_left, append_direction_right]
      change w.direction p = w.direction _
      apply congrArg w.direction
      apply Fin.ext
      have hj : j.val < 1 := j.isLt
      change p.val = p.val + j.val
      omega
  | right j =>
    rw [append_direction_right]
    apply congrArg w.direction
    apply Fin.ext
    rfl

lemma middle_column_cast :
    Fin.cast (whole_length w p)
      (((0 : Fin 1).natAdd (before w p).length).castAdd (after w p).length) = p := by
  apply Fin.ext
  rfl

lemma before_first_empty (p : Fin w.length) (h : p.val = 0) : before w p = empty := by
  apply object_ext _ _ h
  intro j
  have := j.isLt
  change j.val < p.val at this
  omega

lemma after_last_empty (p : Fin w.length) (h : p.val + 1 = w.length) : after w p = empty := by
  have hl : (after w p).length = 0 := by change w.length - p.val - 1 = 0; omega
  apply object_ext _ _ hl
  intro j
  have := j.isLt
  omega

end SerrePositivity.EInfinity.Hammock.Word.ColumnSplit

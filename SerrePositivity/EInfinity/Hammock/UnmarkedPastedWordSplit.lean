module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedColumn
public import SerrePositivity.EInfinity.Hammock.WordColumnSplit
public import SerrePositivity.EInfinity.Hammock.WordCutFactorColumns

/-!
# 元の三因子の語の生成位置での前後の語の回収

概要：元の prefix・一列・残りの語を生成位置で切ると元の前後の語へ戻る。
方針：元の全方向と同じ列番号を照合する。
規約：両側の空語も含む。
使われ方：全図式と元の因子の標準射の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

lemma before_word (a b : Word) : Word.ColumnSplit.before
    (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b) = a := by
  apply Word.object_ext
    (Word.ColumnSplit.before (Word.append (Word.append a (Word.single .forward)) b)
      (columnIndex a b))
    a rfl
  intro j
  change Fin a.length at j
  change (Word.append (Word.append a (Word.single .forward)) b).direction
    ((j.castAdd 1).castAdd b.length) = a.direction j
  exact (Word.append_direction_left (Word.append a (Word.single .forward)) b (j.castAdd 1)).trans
    (Word.append_direction_left a (Word.single .forward) j)

lemma after_word (a b : Word) : Word.ColumnSplit.after
    (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b) = b := by
  have hl : (Word.ColumnSplit.after (Word.append (Word.append a (Word.single .forward)) b)
      (columnIndex a b)).length = b.length := by
    change a.length + 1 + b.length - a.length - 1 = b.length
    omega
  apply Word.object_ext _ _ hl
  intro j
  exact Word.append_direction_right (Word.append a (Word.single .forward)) b (Fin.cast hl j)

lemma prefix_word (a b : Word) : Word.CutFactor.prefixWord
    (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b) =
      Word.append a (Word.single .forward) :=
  congrArg (fun w => Word.append w (Word.single .forward)) (before_word a b)

lemma residual_word (a b : Word) : Word.CutFactor.residualWord
    (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b) =
      Word.append (Word.single .forward) b :=
  congrArg (Word.append (Word.single .forward)) (after_word a b)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted

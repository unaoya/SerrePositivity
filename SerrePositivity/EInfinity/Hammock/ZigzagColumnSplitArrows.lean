module

public import SerrePositivity.EInfinity.Hammock.ZigzagColumnSplitRecovery
public import SerrePositivity.EInfinity.Hammock.WordColumnSplitBlocks

/-!
# 前後の切断図式の元の全列の回収

概要：元の前後の語から切り出した全列を、元の同じ列へ異種等式で照合する。
方針：部分図式の端点移送を除き、元の語の表示変更を回収する。
規約：元の全行と前後の元の列番号を保持する。
使われ方：前後の連続部分の元の区間合成との比較。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram.ColumnSplit
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : Word} {A B : D ⥤ C}
  (p : Fin w.length) (F : MovingDiagram D C W w A B)

lemma before_arrow (d : D) (j : Fin (Word.ColumnSplit.before w p).length) :
    HEq (((before p F).obj d).arrow j)
      ((F.obj d).arrow ((Word.ColumnSplit.beforeBlock w p).column j)) := by
  dsimp only [before, leftPart, ZigzagAppend.Part.leftObj]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact changeWord_arrow_heq (Word.ColumnSplit.whole_eq w p).symm F d _ _ (by
    change 0 + j.val = j.val
    omega)

lemma after_arrow (d : D) (j : Fin (Word.ColumnSplit.after w p).length) :
    HEq (((after p F).obj d).arrow j)
      ((F.obj d).arrow ((Word.ColumnSplit.afterBlock w p).column j)) := by
  dsimp only [after, rightPart, ZigzagAppend.Part.rightObj]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact changeWord_arrow_heq (Word.ColumnSplit.whole_eq w p).symm F d _ _ (by
    change p.val + 1 + j.val = p.val + 1 + j.val
    rfl)

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram.ColumnSplit

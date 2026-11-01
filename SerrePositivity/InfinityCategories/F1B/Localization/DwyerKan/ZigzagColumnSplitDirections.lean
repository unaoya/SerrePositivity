module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitArrows
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.DirectionBlockArrows

/-!
# 元の前後の切断図式の方向付き列

概要：切断図式の前後の全方向付き列を元の同じ列へ照合する。
方針：元の連続部分の全頂点・全列の回収を方向の比較へ代入する。
規約：任意の元の方向と全行を含む。
使われ方：切断因子の横の列の語の作用への比較。
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
  (p : Fin w.length) (F : MovingDiagram D C W w A B) (d : D) (δ : Direction)

lemma before_direction_arrow (i : Fin (Word.ColumnSplit.before w p).length)
    (hi : (Word.ColumnSplit.before w p).direction i = δ) :
    HEq (Direction.arrow δ ((before p F).obj d) i hi)
      (Direction.arrow δ (F.obj d) ((Word.ColumnSplit.beforeBlock w p).column i)
        (((Word.ColumnSplit.beforeBlock w p).direction_eq i).trans hi)) :=
  (Direction.block_arrow_heq (Word.ColumnSplit.beforeBlock w p) ((before p F).obj d) (F.obj d)
    (fun j => (congrArg (F.obj d).vertex (Word.ColumnSplit.beforeBlock_vertex w p j)).trans
      (before_vertex p F d j).symm) (fun j => (before_arrow p F d j).symm) δ i hi).symm

lemma after_direction_arrow (i : Fin (Word.ColumnSplit.after w p).length)
    (hi : (Word.ColumnSplit.after w p).direction i = δ) :
    HEq (Direction.arrow δ ((after p F).obj d) i hi)
      (Direction.arrow δ (F.obj d) ((Word.ColumnSplit.afterBlock w p).column i)
        (((Word.ColumnSplit.afterBlock w p).direction_eq i).trans hi)) :=
  (Direction.block_arrow_heq (Word.ColumnSplit.afterBlock w p) ((after p F).obj d) (F.obj d)
    (fun j => (congrArg (F.obj d).vertex (Word.ColumnSplit.afterBlock_vertex w p j)).trans
      (after_vertex p F d j).symm) (fun j => (after_arrow p F d j).symm) δ i hi).symm

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram.ColumnSplit

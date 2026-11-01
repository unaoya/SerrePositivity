module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitArrows
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SegmentBlockComparison

/-!
# 元の前後の切断図式の区間合成の回収

概要：前後の語で合成した同方向区間を、元の同じ区間へ異種等式で回収する。
方針：元の連続部分の包含と全頂点・全列の回収を区間比較へ代入する。
規約：空区間と任意の方向を含む。
使われ方：切断因子の制限射による横の列の比較。
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

lemma before_segment (u v : Fin ((Word.ColumnSplit.before w p).length + 1)) (huv : u ≤ v)
    (hd : ∀ j : Fin (Word.ColumnSplit.before w p).length,
      u.val ≤ j.val → j.val < v.val → (Word.ColumnSplit.before w p).direction j = δ) :
    HEq (Segment.map δ ((before p F).obj d) u v huv hd)
      (Segment.map δ (F.obj d) ((Word.ColumnSplit.beforeBlock w p).vertex u)
        ((Word.ColumnSplit.beforeBlock w p).vertex v)
        ((Word.ColumnSplit.beforeBlock w p).vertex_monotone huv)
        ((Word.ColumnSplit.beforeBlock w p).interval_direction δ u v hd)) :=
  (Segment.map_block_heq (Word.ColumnSplit.beforeBlock w p) ((before p F).obj d) (F.obj d)
    (fun j => (congrArg (F.obj d).vertex (Word.ColumnSplit.beforeBlock_vertex w p j)).trans
      (before_vertex p F d j).symm) (fun j => (before_arrow p F d j).symm) δ u v huv hd).symm

lemma after_segment (u v : Fin ((Word.ColumnSplit.after w p).length + 1)) (huv : u ≤ v)
    (hd : ∀ j : Fin (Word.ColumnSplit.after w p).length,
      u.val ≤ j.val → j.val < v.val → (Word.ColumnSplit.after w p).direction j = δ) :
    HEq (Segment.map δ ((after p F).obj d) u v huv hd)
      (Segment.map δ (F.obj d) ((Word.ColumnSplit.afterBlock w p).vertex u)
        ((Word.ColumnSplit.afterBlock w p).vertex v)
        ((Word.ColumnSplit.afterBlock w p).vertex_monotone huv)
        ((Word.ColumnSplit.afterBlock w p).interval_direction δ u v hd)) :=
  (Segment.map_block_heq (Word.ColumnSplit.afterBlock w p) ((after p F).obj d) (F.obj d)
    (fun j => (congrArg (F.obj d).vertex (Word.ColumnSplit.afterBlock_vertex w p j)).trans
      (after_vertex p F d j).symm) (fun j => (after_arrow p F d j).symm) δ u v huv hd).symm

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram.ColumnSplit

module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitDiagram

/-!
# 任意列で切り出した図式の元の頂点・列・全縦成分の回収

概要：前・中央・後の図式を元の全頂点と全縦射の同じ位置へ照合する。
方針：元の連結の埋め込みと語の等式による表示変更を使う。
規約：端点も動く元の図式を保持する。
使われ方：非指定列の切断を既存の固定生成矢の図式へ接続する。
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

lemma before_vertex (d : D) (j : Fin ((Word.ColumnSplit.before w p).length + 1)) :
    ((before p F).obj d).vertex j = (F.obj d).vertex (Word.ColumnSplit.beforeVertex w p j) := by
  dsimp only [before, leftPart, ZigzagAppend.Part.leftObj]
  exact changeWord_vertex (Word.ColumnSplit.whole_eq w p).symm F d _ _ rfl

lemma middle_vertex (d : D) (j : Fin ((Word.ColumnSplit.middle w p).length + 1)) :
    ((middle p F).obj d).vertex j = (F.obj d).vertex (Word.ColumnSplit.middleVertex w p j) := by
  dsimp only [middle, leftPart, rightPart, ZigzagAppend.Part.leftObj, ZigzagAppend.Part.rightObj]
  exact changeWord_vertex (Word.ColumnSplit.whole_eq w p).symm F d _ _ rfl

lemma after_vertex (d : D) (j : Fin ((Word.ColumnSplit.after w p).length + 1)) :
    ((after p F).obj d).vertex j = (F.obj d).vertex (Word.ColumnSplit.afterVertex w p j) := by
  dsimp only [after, rightPart, ZigzagAppend.Part.rightObj]
  exact changeWord_vertex (Word.ColumnSplit.whole_eq w p).symm F d _ _ rfl

lemma before_map_app {d e : D} (f : d ⟶ e)
    (j : Fin ((Word.ColumnSplit.before w p).length + 1)) :
    HEq (((before p F).map f).app j)
      ((F.map f).app (Word.ColumnSplit.beforeVertex w p j)) := by
  dsimp only [before, leftPart, leftPartMap]
  exact changeWord_map_app_heq (Word.ColumnSplit.whole_eq w p).symm F f _ _ rfl

lemma middle_map_app {d e : D} (f : d ⟶ e)
    (j : Fin ((Word.ColumnSplit.middle w p).length + 1)) :
    HEq (((middle p F).map f).app j)
      ((F.map f).app (Word.ColumnSplit.middleVertex w p j)) := by
  dsimp only [middle, leftPart, rightPart, leftPartMap, rightPartMap]
  exact changeWord_map_app_heq (Word.ColumnSplit.whole_eq w p).symm F f _ _ rfl

lemma after_map_app {d e : D} (f : d ⟶ e)
    (j : Fin ((Word.ColumnSplit.after w p).length + 1)) :
    HEq (((after p F).map f).app j)
      ((F.map f).app (Word.ColumnSplit.afterVertex w p j)) := by
  dsimp only [after, rightPart, rightPartMap]
  exact changeWord_map_app_heq (Word.ColumnSplit.whole_eq w p).symm F f _ _ rfl

lemma before_arrow_mem (d : D) (j : Fin (Word.ColumnSplit.before w p).length)
    (hm : W ((F.obj d).arrow ⟨j.val, lt_trans j.isLt p.isLt⟩)) :
    W (((before p F).obj d).arrow j) := by
  dsimp only [before, leftPart, ZigzagAppend.Part.leftObj]
  apply (Direction.transport_mem _ _ _).2
  apply (Direction.transport_mem _ _ _).2
  exact changeWord_arrow_mem (Word.ColumnSplit.whole_eq w p).symm F d _ _ rfl hm

lemma middle_arrow {d : D} : HEq (((middle p F).obj d).arrow (0 : Fin 1)) ((F.obj d).arrow p) := by
  dsimp only [middle, leftPart, rightPart, ZigzagAppend.Part.rightObj, ZigzagAppend.Part.leftObj]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact changeWord_arrow_heq (Word.ColumnSplit.whole_eq w p).symm F d _ _ rfl

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram.ColumnSplit

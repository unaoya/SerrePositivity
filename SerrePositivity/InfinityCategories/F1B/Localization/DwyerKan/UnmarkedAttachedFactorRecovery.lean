module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedCutAttachmentDiagrams
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCutFactorVertices

/-!
# 元の切断因子の前後の全頂点・全縦射の回収

概要：prefix の前の語と残りの後の語を元の同じ頂点・縦成分へ照合する。
方針：元の連結の左右の埋め込みと切断前後の回収を合成する。
規約：接合点と空の前後の語を含む。
使われ方：制限した語の射による全因子の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory Zigzag.MovingDiagram Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ [])

lemma prefix_vertex (d : Fin (n.unop.len + 1))
    (k : Fin ((Word.ColumnSplit.before w i).length + 1)) :
    ((prefixDiagram W τ i h).obj d).vertex
      (Word.leftVertex (Word.ColumnSplit.before w i) (Word.single .forward) k) =
        (τ.obj d).vertex (prefixVertex w i k) :=
  (ZigzagAppend.vertex_left ((beforeDiagram W τ i).obj d) ((leftBlock W τ i h).obj d) k).trans
    (ColumnSplit.before_vertex i (ofFunctor τ) d k)

lemma residual_vertex (d : Fin (n.unop.len + 1))
    (k : Fin ((Word.ColumnSplit.after w i).length + 1)) :
    ((residualDiagram W τ i h).obj d).vertex
      (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after w i) k) =
        (τ.obj d).vertex (residualVertex w i k) :=
  (ZigzagAppend.vertex_right ((rightBlock W τ i h).obj d) ((afterDiagram W τ i).obj d) k).trans
    (ColumnSplit.after_vertex i (ofFunctor τ) d k)

lemma prefix_map_app {d e : Fin (n.unop.len + 1)} (f : d ⟶ e)
    (k : Fin ((Word.ColumnSplit.before w i).length + 1)) :
    HEq (((prefixDiagram W τ i h).map f).app
      (Word.leftVertex (Word.ColumnSplit.before w i) (Word.single .forward) k))
      ((τ.map f).app (prefixVertex w i k)) :=
  (ZigzagAppend.Moving.app_left_heq ((beforeDiagram W τ i).map f)
    ((leftBlock W τ i h).map f) k).trans (ColumnSplit.before_map_app i (ofFunctor τ) f k)

lemma residual_map_app {d e : Fin (n.unop.len + 1)} (f : d ⟶ e)
    (k : Fin ((Word.ColumnSplit.after w i).length + 1)) :
    HEq (((residualDiagram W τ i h).map f).app
      (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after w i) k))
      ((τ.map f).app (residualVertex w i k)) :=
  (ZigzagAppend.Moving.app_right_heq ((rightBlock W τ i h).map f)
    ((afterDiagram W τ i).map f)
    (((rightBlock W τ i h).last f).trans ((afterDiagram W τ i).first f).symm) k).trans
      (ColumnSplit.after_map_app i (ofFunctor τ) f k)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments

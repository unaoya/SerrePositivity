module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedAttachedFactorRecovery
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCutFactorCutVertices
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingWordAction
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Diagram

/-!
# 前後の切断因子の元の頂点・縦射と制限した語の作用

概要：prefix の前の語と残りの後の語を、制限射による元の全頂点・縦射へ照合する。
方針：制限射の元の cut と切断因子の前後の回収を合成する。
規約：元の全語の図式と全行を使い、内部切断端点以外の全頂点を含む。
使われ方：全因子の列・内部端点の比較と同じ hammock 余極限の像の一致。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n) (i : Fin a.length)
  (h : column W (τ.obj 0) i ≠ []) (hi : a.direction i = .forward)
  (hT : column W ((((graphDiagram W.paths X Y).map f).app n τ).obj 0) (f.orderHom i) ≠ [])

lemma prefix_action_vertex (d : Fin (n.unop.len + 1))
    (k : Fin ((Word.ColumnSplit.before b (f.orderHom i)).length + 1)) :
    (WordAction.obj (Word.CutFactor.prefixMap f i hi) ((prefixDiagram W τ i h).obj d)).vertex
      (Word.leftVertex (Word.ColumnSplit.before b (f.orderHom i)) (Word.single .forward) k) =
    ((prefixDiagram W (((graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT).obj d).vertex
      (Word.leftVertex (Word.ColumnSplit.before b (f.orderHom i)) (Word.single .forward) k) := by
  change ((prefixDiagram W τ i h).obj d).vertex ((Word.CutFactor.prefixMap f i hi).cut _) = _
  rw [prefix_cut_eq, prefix_vertex W τ i h d (prefixCutVertex f i k),
    prefix_vertex W (((graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT d k,
    prefixCutVertex_original]
  rfl

lemma residual_action_vertex (d : Fin (n.unop.len + 1))
    (k : Fin ((Word.ColumnSplit.after b (f.orderHom i)).length + 1)) :
    (WordAction.obj (Word.CutFactor.residualMap f i hi) ((residualDiagram W τ i h).obj d)).vertex
      (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after b (f.orderHom i)) k) =
    ((residualDiagram W (((graphDiagram W.paths X Y).map f).app n τ)
      (f.orderHom i) hT).obj d).vertex
      (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after b (f.orderHom i)) k) := by
  change ((residualDiagram W τ i h).obj d).vertex ((Word.CutFactor.residualMap f i hi).cut _) = _
  rw [residual_cut_eq, residual_vertex W τ i h d (residualCutVertex f i k),
    residual_vertex W (((graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT d k,
    residualCutVertex_original]
  rfl

lemma prefix_action_app {d e : Fin (n.unop.len + 1)} (g : d ⟶ e)
    (k : Fin ((Word.ColumnSplit.before b (f.orderHom i)).length + 1)) :
    HEq ((WordAction.movingMap (Word.CutFactor.prefixMap f i hi)
      ((prefixDiagram W τ i h).map g)).app
        (Word.leftVertex (Word.ColumnSplit.before b (f.orderHom i)) (Word.single .forward) k))
    (((prefixDiagram W (((graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT).map g).app
      (Word.leftVertex (Word.ColumnSplit.before b (f.orderHom i)) (Word.single .forward) k)) :=
  (Zigzag.MovingHom.app_heq ((prefixDiagram W τ i h).map g) (prefix_cut_eq f i hi k)).trans
    ((prefix_map_app W τ i h g (prefixCutVertex f i k)).trans
      ((Zigzag.app_heq (τ.map g) (prefixCutVertex_original f i k)).trans
        (prefix_map_app W (((graphDiagram W.paths X Y).map f).app n τ)
          (f.orderHom i) hT g k).symm))

lemma residual_action_app {d e : Fin (n.unop.len + 1)} (g : d ⟶ e)
    (k : Fin ((Word.ColumnSplit.after b (f.orderHom i)).length + 1)) :
    HEq ((WordAction.movingMap (Word.CutFactor.residualMap f i hi)
      ((residualDiagram W τ i h).map g)).app
        (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after b (f.orderHom i)) k))
    (((residualDiagram W (((graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT).map g).app
      (Word.rightVertex (Word.single .forward) (Word.ColumnSplit.after b (f.orderHom i)) k)) :=
  (Zigzag.MovingHom.app_heq ((residualDiagram W τ i h).map g) (residual_cut_eq f i hi k)).trans
    ((residual_map_app W τ i h g (residualCutVertex f i k)).trans
      ((Zigzag.app_heq (τ.map g) (residualCutVertex_original f i k)).trans
        (residual_map_app W (((graphDiagram W.paths X Y).map f).app n τ)
          (f.orderHom i) hT g k).symm))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments

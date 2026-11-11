module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedFactorRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorCutVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 前後の切断因子の元の頂点・縦射と制限した語の作用

概要：prefix の前の語と残りの後の語を、制限射による元の全頂点・縦射へ照合する。
方針：制限射の元の cut と切断因子の前後の回収を合成する。
規約：元の全語の図式と全行を使い、内部切断端点以外の全頂点を含む。
使われ方：全因子の列・内部端点の比較と同じ hammock 余極限の像の一致。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n) (i : Fin a.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (hi : a.direction i = .forward)
  (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app n τ).obj 0) (f.orderHom i) ≠ [])

lemma prefix_action_vertex (d : Fin (n.unop.len + 1))
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)).length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f i hi) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).obj d)).vertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) k) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT).obj d).vertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) k) := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).obj d).vertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f i hi).cut _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_cut_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_vertex W τ i h d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixCutVertex f i k),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_vertex W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT d k,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixCutVertex_original]
  rfl

lemma residual_action_vertex (d : Fin (n.unop.len + 1))
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).obj d)).vertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)) k) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app n τ)
      (f.orderHom i) hT).obj d).vertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)) k) := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).obj d).vertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_vertex W τ i h d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex f i k),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_vertex W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT d k,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex_original]
  rfl

lemma prefix_action_app {d e : Fin (n.unop.len + 1)} (g : d ⟶ e)
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)).length + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f i hi)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).map g)).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) k))
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT).map g).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) k)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).map g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_cut_eq f i hi k)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_map_app W τ i h g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixCutVertex f i k)).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.app_heq (τ.map g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixCutVertex_original f i k)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_map_app W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app n τ)
          (f.orderHom i) hT g k).symm))

lemma residual_action_app {d e : Fin (n.unop.len + 1)} (g : d ⟶ e)
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).length + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).map g)).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)) k))
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app n τ) (f.orderHom i) hT).map g).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)) k)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).map g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut_eq f i hi k)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_map_app W τ i h g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex f i k)).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.app_heq (τ.map g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex_original f i k)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_map_app W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app n τ)
          (f.orderHom i) hT g k).symm))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

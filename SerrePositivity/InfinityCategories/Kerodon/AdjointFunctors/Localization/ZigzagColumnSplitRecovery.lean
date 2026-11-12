module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram

/-!
# 任意列で切り出した図式の元の頂点・列・全縦成分の回収

概要：前・中央・後の図式を元の全頂点と全縦射の同じ位置へ照合する。
方針：元の連結の埋め込みと語の等式による表示変更を使う。
規約：端点も動く元の図式を保持する。
使われ方：非指定列の切断を既存の固定生成矢の図式へ接続する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C}
  (p : Fin w.length) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B)

lemma before_vertex (d : D) (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before p F).obj d).vertex j = (F.obj d).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeVertex w p j) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.leftPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F d _ _ rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.before_vertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (before_vertex)


lemma middle_vertex (d : D) (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p).length + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle p F).obj d).vertex j = (F.obj d).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.middleVertex w p j) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.leftPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.rightPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F d _ _ rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.middle_vertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (middle_vertex)


lemma after_vertex (d : D) (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p).length + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after p F).obj d).vertex j = (F.obj d).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterVertex w p j) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.rightPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F d _ _ rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.after_vertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (after_vertex)


lemma before_map_app {d e : D} (f : d ⟶ e)
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length + 1)) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before p F).map f).app j)
      ((F.map f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeVertex w p j)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.leftPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.leftPartMap]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_map_app_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F f _ _ rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.before_map_app export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (before_map_app)


lemma middle_map_app {d e : D} (f : d ⟶ e)
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.middle w p).length + 1)) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle p F).map f).app j)
      ((F.map f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.middleVertex w p j)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.leftPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.rightPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.leftPartMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.rightPartMap]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_map_app_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F f _ _ rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.middle_map_app export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (middle_map_app)


lemma after_map_app {d e : D} (f : d ⟶ e)
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p).length + 1)) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after p F).map f).app j)
      ((F.map f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterVertex w p j)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.rightPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.rightPartMap]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_map_app_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F f _ _ rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.after_map_app export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (after_map_app)


lemma before_arrow_mem (d : D) (j : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length)
    (hm : W ((F.obj d).arrow ⟨j.val, lt_trans j.isLt p.isLt⟩)) :
    W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before p F).obj d).arrow j) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.leftPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_arrow_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F d _ _ rfl hm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.before_arrow_mem export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (before_arrow_mem)


lemma middle_arrow {d : D} : HEq (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle p F).obj d).arrow (0 : Fin 1)) ((F.obj d).arrow p) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.leftPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts.rightPart, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_arrow_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F d _ _ rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.middle_arrow export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (middle_arrow)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

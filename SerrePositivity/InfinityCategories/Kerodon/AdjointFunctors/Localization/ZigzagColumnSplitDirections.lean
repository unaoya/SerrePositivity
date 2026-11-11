module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitArrows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionBlockArrows

/-!
# 元の前後の切断図式の方向付き列

概要：切断図式の前後の全方向付き列を元の同じ列へ照合する。
方針：元の連続部分の全頂点・全列の回収を方向の比較へ代入する。
規約：任意の元の方向と全行を含む。
使われ方：切断因子の横の列の語の作用への比較。

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
  (p : Fin w.length) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B) (d : D) (δ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)

lemma before_direction_arrow (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).length)
    (hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w p).direction i = δ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before p F).obj d) i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ (F.obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w p).column i)
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w p).direction_eq i).trans hi)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.block_arrow_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock w p) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before p F).obj d) (F.obj d)
    (fun j => (congrArg (F.obj d).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock_vertex w p j)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_vertex p F d j).symm) (fun j => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_arrow p F d j).symm) δ i hi).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.before_direction_arrow export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (before_direction_arrow)


lemma after_direction_arrow (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p).length)
    (hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w p).direction i = δ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after p F).obj d) i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ (F.obj d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w p).column i)
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w p).direction_eq i).trans hi)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.block_arrow_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock w p) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after p F).obj d) (F.obj d)
    (fun j => (congrArg (F.obj d).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock_vertex w p j)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.after_vertex p F d j).symm) (fun j => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.after_arrow p F d j).symm) δ i hi).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.after_direction_arrow export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (after_direction_arrow)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

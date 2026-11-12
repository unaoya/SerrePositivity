module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramPrecomp
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramOfFunctor

/-!
# 動く全図式の切断・連結・表示変更と再添字

概要：元の全図式の前合成は、語の表示変更・部分区間・連結を保持する。
方針：全対象・全縦射の定義を回収し、語の等式の帰納を使う。
規約：元の端点関手も同時に前合成する。
使われ方：prefix・残りの図式と元の全単体作用素。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD uI vI
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {I : Type uI} [Category.{vI} I]
  {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B E : D ⥤ C} (K : I ⥤ D)

lemma changeWord_precomp (h : a = b) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord h F).precomp K = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord h (F.precomp K) := by cases h; rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (changeWord_precomp)


lemma append_precomp (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b B E) :
    (F.append G).precomp K = (F.precomp K).append (G.precomp K) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_precomp)


lemma leftPart_precomp (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) A E) :
    (F.precomp K).leftPart = F.leftPart.precomp K := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (leftPart_precomp)


lemma rightPart_precomp (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) A E) :
    (F.precomp K).rightPart = F.rightPart.precomp K := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (rightPart_precomp)


lemma ofFunctor_precomp {X Y : C} (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor (K ⋙ F) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor F).precomp K := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (ofFunctor_precomp)


namespace ColumnSplit
variable {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C} (p : Fin w.length) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B)

lemma expanded_precomp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.expanded p (F.precomp K) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.expanded p F).precomp K :=
  (changeWord_precomp K (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.expanded_precomp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit (expanded_precomp)


lemma before_precomp : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before p (F.precomp K)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before p F).precomp K) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before]
  rw [expanded_precomp, leftPart_precomp, leftPart_precomp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.before_precomp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit (before_precomp)


lemma middle_precomp : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle p (F.precomp K)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle p F).precomp K) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.middle]
  rw [expanded_precomp, leftPart_precomp, rightPart_precomp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.middle_precomp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit (middle_precomp)


lemma after_precomp : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after p (F.precomp K)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after p F).precomp K) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after]
  rw [expanded_precomp, rightPart_precomp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.after_precomp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit (after_precomp)


end ColumnSplit
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

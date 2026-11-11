module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramOfFunctor

/-!
# 任意列の前後の全図式から元の固定端点の関手を回収する

概要：元の固定端点の関手を切り、貼り戻すと同じ全対象・全射の関手に戻る。
方針：MovingDiagram の厳密な貼り戻しと元の ofFunctor の回収を使う。
規約：添字圏は任意で、全行と全縦射を保持する。
使われ方：元の hammock graph の任意列での分割・貼り戻し。

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
  {W : MorphismProperty C} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma ofFunctor_fixedFunctor (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor F).fixedFunctor = F := by
  apply CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro d e f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (ofFunctor_fixedFunctor)


namespace ColumnSplit

def recombinedFunctor (p : Fin w.length) (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.recombine p (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor F)).fixedFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.recombinedFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit (recombinedFunctor)


lemma recombinedFunctor_eq (p : Fin w.length) (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    recombinedFunctor p F = F := by
  rw [recombinedFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.recombine_eq, ofFunctor_fixedFunctor]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.recombinedFunctor_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit (recombinedFunctor_eq)


end ColumnSplit
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

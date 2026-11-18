module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramDiagonalLabels

/-!
# 元の部分対角の比較射と両ラベルの比較

概要：元の比較射は同じ底と両係数で要素圏の全射列を送る。
方針：元の係数自然変換の nerve の成分を使う。
規約：元の chainRowMap 自身を全次数で回収する。
使われ方：DK10.6(ii)の Hom 積の和の同型の下での比較射の照合。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram
open _root_.CategoryTheory

variable {D E : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} (τ : D ⟶ E) (n : SimplexCategoryᵒᵖ)

def leftLabelComparison : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels D n ⟶ (τ.app n).base.op ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels E n where
  app w := ↾fun a => a ⋙ ((τ.app n).left.app w).toFunctor
  naturality w w' h := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg (fun K => a ⋙ Cat.Hom.toFunctor K) ((τ.app n).left.naturality h)

def rightLabelComparison : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels D n ⟶ (τ.app n).base ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels E n where
  app w := ↾fun a => a ⋙ ((τ.app n).right.app w).toFunctor
  naturality w w' h := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg (fun K => a ⋙ Cat.Hom.toFunctor K) ((τ.app n).right.naturality h)

lemma chainRowMap_app (k : SimplexCategoryᵒᵖ)
    (e : ComposableArrows (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.labelCategory D n) k.unop.len) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.chainRowMap τ k).app n e =
      e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabelComparison τ n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabelComparison τ n) ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pre (τ.app n).base (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels E n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels E n) := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram

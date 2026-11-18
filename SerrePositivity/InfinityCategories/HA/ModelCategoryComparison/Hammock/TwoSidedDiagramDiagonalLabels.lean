module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramPartialRows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates
/-!
# 部分対角に沿う元の両ラベルと全作用素

概要：次数とラベル次数が同時に動く部分対角の作用を元の要素圏の射で表す。
方針：元の係数関手と同じ単体作用素の前合成を組み合わせる。
規約：元の chainRow の作用素そのものを全単体で回収する。
使われ方：DK10.6(ii)の Hom 因子分解の全作用素への整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram
open _root_.CategoryTheory _root_.Opposite
variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u})
def leftLabels (n : SimplexCategoryᵒᵖ) : (D.obj n).baseᵒᵖ ⥤ Type u :=
  ((D.obj n).left ⋙ nerveFunctor).flip.obj n

def rightLabels (n : SimplexCategoryᵒᵖ) : (D.obj n).base ⥤ Type u :=
  ((D.obj n).right ⋙ nerveFunctor).flip.obj n

def leftLabelsMap {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels D n ⟶ (D.map θ).base.op ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels D m where
  app w := ↾fun a => (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ a ⋙
    ((D.map θ).left.app w).toFunctor
  naturality w w' h := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg (fun K => (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ a ⋙
      Cat.Hom.toFunctor K) ((D.map θ).left.naturality h)

def rightLabelsMap {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels D n ⟶ (D.map θ).base ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels D m where
  app w := ↾fun a => (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ a ⋙
    ((D.map θ).right.app w).toFunctor
  naturality w w' h := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg (fun K => (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ a ⋙
      Cat.Hom.toFunctor K) ((D.map θ).right.naturality h)

abbrev labelCategory (n : SimplexCategoryᵒᵖ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels D n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels D n)

def labelStep {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.labelCategory D n ⥤ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.labelCategory D m :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabelsMap D θ) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabelsMap D θ) ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pre (D.map θ).base (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels D m) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels D m)

lemma chainRow_map (k : SimplexCategoryᵒᵖ) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (e : ComposableArrows (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.labelCategory D n) k.unop.len) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.chainRow D k).map θ e = e ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.labelStep D θ := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram

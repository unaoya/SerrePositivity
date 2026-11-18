module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGridRootHull

/-!
# 元の固定語の各単体の有限包への持ち上げ

概要：元の全体の各 grid は同じ有限部分集合図式の一項の像となる。
方針：元の全射列の支持と既存の厳密な grid の回収式を使う。
規約：元の同じ語と単体次数を保持する。
使われ方：固定語の graph の余極限の全射性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite
open _root_.CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n : SimplexCategoryᵒᵖ)

def liftSimplex (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (⊤ : MorphismProperty (Paths Q)) a
    ((Paths.of Q).obj X) ((Paths.of Q).obj Y)).obj n) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport σ)).obj n := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport σ))
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.rootedFunctor T σ

lemma liftSimplex_projection (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (⊤ : MorphismProperty (Paths Q)) a
    ((Paths.of Q).obj X) ((Paths.of Q).obj Y)).obj n) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphCocone T X Y a).ι.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport σ)).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.liftSimplex T X Y a n σ) = σ := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport σ))
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.rootedFunctor_projection T σ

lemma graphMap_projection {S R : Finset Q} (h : S ⊆ R) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a).map (homOfLE h) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a R) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a S) := by
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.mapFunctor T X Y a h) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a R) = _
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.mapFunctor T X Y a h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a R) = _
  exact congrArg nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mapFunctor_projection T X Y a h)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite

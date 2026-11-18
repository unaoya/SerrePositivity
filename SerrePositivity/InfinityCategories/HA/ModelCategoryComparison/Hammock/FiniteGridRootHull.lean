module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeEndpointHull
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTreeFiniteContractible

/-!
# 元の全有限 grid の根に閉じた有限部分木への因子化

概要：元の両端と全横縦射列を一つの根に閉じた有限部分木に入れる。
方針：全射列の実際の支持の endpointHull に関手を持ち上げる。
規約：射影後は元の全 grid の同じ関手へ厳密に戻る。
使われ方：全被覆の hammock の各単体の有限支持と可縮性の移送。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] {I : Type w} [Category.{w'} I]
  [Fintype I] [∀ i j : I, Fintype (i ⟶ j)] {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths Q}
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) a X Y)

def hull : Finset Q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F)

def leftVertex : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F) :=
  ⟨X, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_left T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F)⟩

def rightVertex : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F) :=
  ⟨Y, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_right T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F)⟩

def rootedFunctor : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F)
    I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F)))) a
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F))).obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.leftVertex T F))
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F))).obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.rightVertex T F)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridFunctor.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F) F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_left T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_right T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subset_endpointHull T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F))

lemma rootedFunctor_projection : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F)
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.rootedFunctor T F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathRelative (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F)) = F := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridFunctor.functor_projection (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F) F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_left T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_right T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subset_endpointHull T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F))

lemma rootedHammock_isWeaklyContractible [Quiver.IsThin (Quiver.FreeGroupoid Q)] :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F)
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
      (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F))))
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F))).obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.leftVertex T F))
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F))).obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.rightVertex T F))) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F)
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.finite_colimit_isWeaklyContractible T (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid.hull T F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_closed T X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F)) _ _

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteGrid

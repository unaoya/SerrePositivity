module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedProductComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackKanObjects
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.EdgeApexPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：元の全空間積比較を、その同じ coherent な辺の頂点円柱にする。
方針：両対象を既存の Kan 模型に束ね、元の比較を辺として保つ。
規約：sifted 性は可逆性にだけ使用。使われ方：native な積錐の指定頂点輸送。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
variable {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)

/-- 元の全空間積比較を元の Kan 対象間の射として保持する。 -/
def totalProductComparisonKanMap :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (pullback p q) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E)).obj (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison p q

/-- 元の比較辺を、その全一単体を保つ頂点円柱にする。 -/
def totalProductComparisonApexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (totalProductComparisonKanMap p q))

/-- 頂点円柱の始点は元の fiber ごとの積の全空間 Kan 模型。 -/
lemma totalProductComparisonApexPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[0] : SSet.{u + 1}) ≫ totalProductComparisonApexPrism p q =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (pullback p q))) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_zero _

/-- 頂点円柱の終点は元の二全空間の Kan 模型の直積。 -/
lemma totalProductComparisonApexPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[0] : SSet.{u + 1}) ≫ totalProductComparisonApexPrism p q =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E)).obj (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D))) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_one _

/-- sifted な底上の元の比較の頂点円柱は、全ての垂直辺が可逆。 -/
lemma totalProductComparisonApexPrism_vertical_isInvertible [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (x : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((totalProductComparisonApexPrism p q).app
      (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj D)
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_vertical_isInvertible _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalKanProductComparison_homotopyEquivalence_of_sifted p q).isQCatEquivalence) x

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

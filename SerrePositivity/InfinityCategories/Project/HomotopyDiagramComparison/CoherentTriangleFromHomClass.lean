module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTriangleFromFunctorSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IntervalVertexHomotopy

/-!
概要：元の変換の合成類の等式を、同じ指定長辺を持つ全変換三角形へ持ち上げる。
方針：元の三変換から辺を回収し、quasicategory の合成二単体を選ぶ。
規約：長辺の変換を選び直さず、三つの変換と全三角形を保持する。
使われ方：標準単位正方形から元の全余錐への比較を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SSet.Truncated.HomotopyCategory
variable {B : SSet.{u + 1}} {F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
  (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F J) _⦋0⦌)
  (h : homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex x).toTruncated ≫
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex y).toTruncated =
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex l).toTruncated)

/-- 元の三変換の合成類の等式を、同じ長辺を持つ全変換三角形で実現する。 -/
def coherentTransformationTriangleOfHomClass :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationVertexTriangle F G J x y := by
  let σ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.compStructOfHomotopyCategoryFac h
  let T := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTriangleOfFunctorSimplex σ
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex x) = x :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).apply_symm_apply x
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex y) = y :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).apply_symm_apply y
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex l) = l :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).apply_symm_apply l
  have hl' : T.diagonal = l := hl
  exact {
    diagonal := l
    diagram := T.diagram
    first := by simpa only [hx] using T.first
    second := by simpa only [hy] using T.second
    long := by simpa only [hl'] using T.long }

/-- 同じ合成類の等式から構成した三角形の長辺は、元の指定変換そのもの。 -/
lemma coherentTransformationTriangleOfHomClass_diagonal :
    (coherentTransformationTriangleOfHomClass x y l h).diagonal = l := rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTriangleFromFunctorSimplex
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalVertexHomotopy

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (l : (leftUnstraighteningTransformationSpace F J) _⦋0⦌)
  (h : homMk (intervalMappingEdgeOfVertex x).toTruncated ≫
    homMk (intervalMappingEdgeOfVertex y).toTruncated =
      homMk (intervalMappingEdgeOfVertex l).toTruncated)

/-- 元の三変換の合成類の等式を、同じ長辺を持つ全変換三角形で実現する。 -/
def coherentTransformationTriangleOfHomClass :
    F2.CoherentTransformationVertexTriangle F G J x y := by
  let σ := compStructOfHomotopyCategoryFac h
  let T := coherentTransformationTriangleOfFunctorSimplex σ
  have hx : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex x) = x :=
    (intervalMappingEdgeVertexEquiv _ _).apply_symm_apply x
  have hy : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex y) = y :=
    (intervalMappingEdgeVertexEquiv _ _).apply_symm_apply y
  have hl : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex l) = l :=
    (intervalMappingEdgeVertexEquiv _ _).apply_symm_apply l
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

end SerrePositivity.InfinityCategories.HomotopyLimits

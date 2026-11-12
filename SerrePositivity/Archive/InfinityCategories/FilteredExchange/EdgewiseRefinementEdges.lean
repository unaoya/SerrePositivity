module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.EdgewiseRefinementEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-!
概要：元の精密化の二つの共通解像を、同じ共通終点を持つ実際の辺にする。
方針：実両面の式を辺の両端へ入力し、必要な宇宙へ同じ辺を持ち上げる。
規約：辺の代表と元の一単体を保持する。
使われ方：左右区間比較の自然性の二正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 始点に定値な係数から元の精密化への実右解像の辺。 -/
def edgewiseRefinementRightEdge {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseSubdivision X).Edge
      (edgewiseRefinementVertex (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e))
      (edgewiseRefinementVertex e) where
  edge := edgewiseRefinementRightResolution e
  src_eq := edgewiseRefinementRightResolution_source e
  tgt_eq := edgewiseRefinementRightResolution_target e

/-- 終点に定値な係数から元の精密化への実左解像の辺。 -/
def edgewiseRefinementLeftEdge {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseSubdivision X).Edge
      (edgewiseRefinementVertex (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e))
      (edgewiseRefinementVertex e) where
  edge := edgewiseRefinementLeftResolution e
  src_eq := edgewiseRefinementLeftResolution_source e
  tgt_eq := edgewiseRefinementLeftResolution_target e

/-- 右解像の同じ実辺を、両端を含めて必要な宇宙へ持ち上げる。 -/
def edgewiseRefinementRightEdgeUlift {X : SSet.{u}} (e : X _⦋1⦌) :
    ((SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X)).Edge
      (ULift.up (edgewiseRefinementVertex
        (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e)))
      (ULift.up (edgewiseRefinementVertex e)) :=
  SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, v} (edgewiseRefinementRightEdge e).toTruncated)

/-- 左解像の同じ実辺を、同じ共通終点とともに必要な宇宙へ持ち上げる。 -/
def edgewiseRefinementLeftEdgeUlift {X : SSet.{u}} (e : X _⦋1⦌) :
    ((SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X)).Edge
      (ULift.up (edgewiseRefinementVertex
        (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e)))
      (ULift.up (edgewiseRefinementVertex e)) :=
  SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, v} (edgewiseRefinementLeftEdge e).toTruncated)

end SerrePositivity.InfinityCategories.F2

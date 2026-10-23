module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitBoundaryComparisonSquare
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitInteriorTriangles
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitTetrahedronFirstEdges

/-!
概要：元の 中央の 単位三単体の四面・六辺を、元の指定三角形のまま境界データにする。
方針：元の外側面と同じ内部面の等式を用い、比較も三角形も再選択しない。
規約：元の三単体を保持。使われ方：四面の指定比較の可換性の具体化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の中央の単位三単体の、同じ指定四面・六辺を持つ境界データ。 -/
def coherentColimitUnitMiddleBoundary : CoherentColimitUnitTetrahedronBoundary B T 1 where
  vertex1 := G
  vertex2 := SSet.const (coherentDiagramTotalCocone G).vertex
  vertex3 := SSet.const (coherentDiagramTotalCocone J).vertex
  edge01 := l
  edge12 := coconeTransformationHomotopy (coherentDiagramTotalCocone G)
  edge23 := simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B r)
  edge02 := coherentColimitUnitDiagonal B l
  edge13 := coherentColimitUnitDiagonal B r
  edge03 := coherentColimitUnitDiagonal B d
  triangle012 := coherentColimitUnitUpperTriangle B l
  triangle123 := coherentColimitUnitLowerTriangle B r
  triangle013 := coherentColimitUnitInteriorLast B T
  triangle023 := coherentColimitUnitInteriorFirst B T
  firstEdge := coherentColimitUnitTetrahedron_middle_firstEdge B T
  face012 := coherentColimitUnitTetrahedron_lower_first B T
  face123 := coherentColimitUnitTetrahedron_upper_last B T
  face013 := (coherentColimitUnitTriangleTetrahedron_glue_last B T).trans
    (coherentColimitUnitInteriorLast_face B T)
  face023 := (coherentColimitUnitTriangleTetrahedron_glue_first B T).symm.trans
    (coherentColimitUnitInteriorFirst_face B T)

end SerrePositivity.InfinityCategories.F2

module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitBoundaryComparisonSquare
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitInteriorTriangles
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitTetrahedronFirstEdges

/-!
概要：元の 最後の 単位三単体の四面・六辺を、元の指定三角形のまま境界データにする。
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

/-- 元の最後の単位三単体の、同じ指定四面・六辺を持つ境界データ。 -/
def coherentColimitUnitLastBoundary : CoherentColimitUnitTetrahedronBoundary B T 2 where
  vertex1 := G
  vertex2 := J
  vertex3 := SSet.const (coherentDiagramTotalCocone J).vertex
  edge01 := l
  edge12 := r
  edge23 := coconeTransformationHomotopy (coherentDiagramTotalCocone J)
  edge02 := d
  edge13 := coherentColimitUnitDiagonal B r
  edge03 := coherentColimitUnitDiagonal B d
  triangle012 := T
  triangle123 := coherentColimitUnitUpperTriangle B r
  triangle013 := coherentColimitUnitInteriorLast B T
  triangle023 := coherentColimitUnitUpperTriangle B d
  firstEdge := coherentColimitUnitTetrahedron_last_firstEdge B T
  face012 := coherentColimitUnitTriangleTetrahedron_last B T
  face123 := coherentColimitUnitTetrahedron_lower_last B T
  face013 := coherentColimitUnitInteriorLast_face B T
  face023 := coherentColimitUnitTetrahedron_lower_long B T

end SerrePositivity.InfinityCategories.F2

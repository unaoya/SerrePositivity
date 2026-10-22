module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitBoundaryComparisonSquare
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitInteriorTriangles
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitTetrahedronFirstEdges

/-!
概要：元の 最初の 単位三単体の四面・六辺を、元の指定三角形のまま境界データにする。
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

/-- 元の最初の単位三単体の、同じ指定四面・六辺を持つ境界データ。 -/
def coherentColimitUnitFirstBoundary : CoherentColimitUnitTetrahedronBoundary B T 0 where
  vertex1 := SSet.const (coherentDiagramTotalCocone F).vertex
  vertex2 := SSet.const (coherentDiagramTotalCocone G).vertex
  vertex3 := SSet.const (coherentDiagramTotalCocone J).vertex
  edge01 := coconeTransformationHomotopy (coherentDiagramTotalCocone F)
  edge12 := simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B l)
  edge23 := simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B r)
  edge02 := coherentColimitUnitDiagonal B l
  edge13 := simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B d)
  edge03 := coherentColimitUnitDiagonal B d
  triangle012 := coherentColimitUnitLowerTriangle B l
  triangle123 := coherentColimitConstantTriangle B T
  triangle013 := coherentColimitUnitLowerTriangle B d
  triangle023 := coherentColimitUnitInteriorFirst B T
  firstEdge := by
    have hs : stdSimplex.δ (3 : Fin 4) ≫
        SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T 0) =
          (coherentColimitUnitLowerTriangle B l).diagram := by
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact coherentColimitUnitTetrahedron_upper_first B T
    rw [Category.assoc, hs, (coherentColimitUnitLowerTriangle B l).face_two]
  face012 := coherentColimitUnitTetrahedron_upper_first B T
  face123 := coherentColimitUnitTriangleTetrahedron_first B T
  face013 := coherentColimitUnitTetrahedron_upper_long B T
  face023 := coherentColimitUnitInteriorFirst_face B T

end SerrePositivity.InfinityCategories.F2

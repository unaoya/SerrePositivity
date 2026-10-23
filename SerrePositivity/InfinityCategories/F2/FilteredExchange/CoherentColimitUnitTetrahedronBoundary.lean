module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitSharedFirstEdge
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitSharedInitialDiagonalEdge
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitSharedMiddleDiagonalEdge
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitSharedMiddleEdge
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitSharedLastEdge

/-!
概要：元の単位三単体の四面を、共通の六つの指定辺と元の面の等式で保持する。
方針：元の三単体の実際の面・辺のみを境界データとして束ねる。
規約：比較の合成則をデータに仮定しない。使われ方：全族の四面の比較を共通頂点へ揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の同じ単位三単体の四面と六辺を厳密に表示する境界データ。 -/
structure CoherentColimitUnitTetrahedronBoundary (B : SSet.{u})
    {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
    (T : FunctorCompositionTriangle l r d) (k : Fin 3) where
  vertex1 : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}
  vertex2 : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}
  vertex3 : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}
  edge01 : SSet.Homotopy F vertex1
  edge12 : SSet.Homotopy vertex1 vertex2
  edge23 : SSet.Homotopy vertex2 vertex3
  edge02 : SSet.Homotopy F vertex2
  edge13 : SSet.Homotopy vertex1 vertex3
  edge03 : SSet.Homotopy F vertex3
  triangle012 : FunctorCompositionTriangle edge01 edge12 edge02
  triangle123 : FunctorCompositionTriangle edge12 edge23 edge13
  triangle013 : FunctorCompositionTriangle edge01 edge13 edge03
  triangle023 : FunctorCompositionTriangle edge02 edge23 edge03
  firstEdge : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry edge01.h
  face012 : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 3
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv triangle012.diagram
  face123 : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv triangle123.diagram
  face013 : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 2
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv triangle013.diagram
  face023 : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 1
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv triangle023.diagram

end SerrePositivity.InfinityCategories.F2

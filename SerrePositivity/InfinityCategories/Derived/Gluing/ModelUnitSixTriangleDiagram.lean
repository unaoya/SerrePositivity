module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitSixTriangleDiagramCancellation
/-! # 正本 Hom 模型上の実六片の型付き図式

概要：六つの元二単体を、実補正辺と実係数辺の五頂点図式へ接続する。
方針：既存の全共有辺の照合を用い、中間頂点も係数三角形から回収する。
規約：主経路の元 Hom 模型・二単体・辺の代表を厳密に保持する。
使われ方：単位閉路の零性を実六片の消去へ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingModelUnitSixTriangleDiagram :=
  dgGluingUnitSixTriangleDiagramOfEdges
    (dgGluingModelUnitCapTriangleDiagram R C D M X Y)
    (functorEdgeOfSimplicialHomotopy (dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y))
    (functorEdgeOfSimplicialHomotopy (dgGluingLastCapDiagonalSpanHomotopy R C D M X Y))
    (dgGluingModelUnitCapCoefficientEdge R C D M X Y)
    (congrArg SSet.yonedaEquiv
      (dgGluingModelUnitCapTriangleDiagram_first_cap R C D M X Y))
    (congrArg SSet.yonedaEquiv
      (dgGluingModelUnitCapTriangleDiagram_last_cap R C D M X Y))
    (dgGluingModelUnitCapCoefficientEdge_edge R C D M X Y).symm
    (dgGluingModelUnitCapTriangleDiagram_first_diagonal R C D M X Y)
    (dgGluingModelUnitCapTriangleDiagram_last_diagonal R C D M X Y)
    (dgGluingModelUnitCapTriangleDiagram_first_bridge R C D M X Y)
    (dgGluingModelUnitCapTriangleDiagram_last_bridge R C D M X Y)
    (dgGluingModelUnitCapTriangleDiagram_coefficient_first R C D M X Y)
    (dgGluingModelUnitCapTriangleDiagram_coefficient_last R C D M X Y)
end SerrePositivity.InfinityCategories

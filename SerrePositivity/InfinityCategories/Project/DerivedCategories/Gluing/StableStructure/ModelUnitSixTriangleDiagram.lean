module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.UnitSixTriangleDiagramCancellation
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

def dgGluingModelUnitSixTriangleDiagram :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSixTriangleDiagramOfEdges
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastCapDiagonalSpanHomotopy R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapCoefficientEdge R C D M X Y)
    (congrArg SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_first_cap R C D M X Y))
    (congrArg SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_last_cap R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapCoefficientEdge_edge R C D M X Y).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_first_diagonal R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_last_diagonal R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_first_bridge R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_last_bridge R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_coefficient_first R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_coefficient_last R C D M X Y)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

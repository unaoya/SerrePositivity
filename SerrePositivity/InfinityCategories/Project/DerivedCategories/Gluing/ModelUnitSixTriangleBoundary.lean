module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModelUnitSixTriangleDiagram
/-! # 正本実六片の単位類から指定対角境界へ

概要：実六片の二つの単位辺の零性を、正本の指定三辺の実充填へ移す。
方針：元の二補正辺・係数辺・橋を照合し、同じ六二単体の六角形関係を消去する。
規約：単位辺の零性だけを補助入力として隔離し、主経路の公開界面を変更しない。
使われ方：D の厳密単位則と F1B の相対比較の供給を、③から④へ接続する。
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

lemma dgGluingModelUnitSixTriangle_first_cap_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 0 2 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y) := by
  apply Truncated.Edge.ext
  exact congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_first_cap R C D M X Y)

lemma dgGluingModelUnitSixTriangle_last_cap_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 2 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastCapDiagonalSpanHomotopy R C D M X Y) := by
  apply Truncated.Edge.ext
  exact congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_last_cap R C D M X Y)

lemma dgGluingModelUnitSixTriangle_coefficient_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 4 1 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapCoefficientEdge R C D M X Y := by
  apply Truncated.Edge.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapCoefficientEdge_edge R C D M X Y).symm

lemma dgGluingModelUnitSixTriangle_bridge_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 5 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarBridgeHomotopy R C D M X Y) := by
  apply Truncated.Edge.ext
  change SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram R C D M X Y 5) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram_collar_bridge R C D M X Y]
  exact congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarCompositionTriangle R C D M X Y).face_one

lemma dgGluingModelUnitSixTriangle_coefficient_iso :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edgeIso 4 1 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapCoefficientIso R C D M X Y := by
  apply Iso.ext
  change Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 4 1) =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapCoefficientEdge R C D M X Y)
  exact congrArg (fun e => Truncated.HomotopyCategory.homMk e)
    (dgGluingModelUnitSixTriangle_coefficient_edge R C D M X Y)

lemma dgGluingLaxHomDiagonalComparisonBoundary_filling_of_model_unit_classes
    (hr : Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 0 0) = 𝟙 _)
    (hl : Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 2 2) = 𝟙 _) :
    ∃ V, (boundary 2).ι ≫ V = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomDiagonalComparisonBoundary_filling_of_actual_unit_hexagon R C D M X Y
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).hexagon_of_unit_classes_transport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastCapDiagonalSpanHomotopy R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarBridgeHomotopy R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapCoefficientIso R C D M X Y)
    (dgGluingModelUnitSixTriangle_first_cap_edge R C D M X Y)
    (dgGluingModelUnitSixTriangle_last_cap_edge R C D M X Y)
    (dgGluingModelUnitSixTriangle_bridge_edge R C D M X Y)
    (dgGluingModelUnitSixTriangle_coefficient_iso R C D M X Y) hr hl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

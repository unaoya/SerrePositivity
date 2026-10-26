module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitSixTriangleDiagramCancellation
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapCoefficientFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitSpanTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitSpanRelativeComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleDiagrams
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCollarIntervalTriangle
/-!
概要：元終域の六片を五頂点の型付き図式として保持する。
方針：元の全入力・指定面・全区間族を保持する比較を合成する。
規約：追加の主経路仮定を置かない。使われ方：元 lax Hom 比較の逆の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetUnitCapCoefficientEdge :=
  functorEdgeOfSimplicialHomotopy
    (dgGluingHomTargetAugmentationDiagonalHomotopy R C D E p q X Y)

lemma dgGluingHomTargetUnitCapCoefficientEdge_edge :
    (dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y).edge =
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫
        dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 4) :=
  congrArg SSet.yonedaEquiv
    (dgGluingHomTargetUnitCapTriangleDiagram_coefficient_homotopy R C D E p q X Y).symm

def dgGluingHomTargetUnitSixTriangleDiagram :=
  dgGluingUnitSixTriangleDiagramOfEdges
    (dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y)
    (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y))
    (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y))
    (dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y)
    (congrArg SSet.yonedaEquiv
      (dgGluingHomTargetUnitCapTriangleDiagram_first_cap R C D E p q X Y))
    (congrArg SSet.yonedaEquiv
      (dgGluingHomTargetUnitCapTriangleDiagram_last_cap R C D E p q X Y))
    (dgGluingHomTargetUnitCapCoefficientEdge_edge R C D E p q X Y).symm
    (dgGluingHomTargetUnitCapTriangleDiagram_first_diagonal R C D E p q X Y)
    (dgGluingHomTargetUnitCapTriangleDiagram_last_diagonal R C D E p q X Y)
    (dgGluingHomTargetUnitCapTriangleDiagram_first_bridge R C D E p q X Y)
    (dgGluingHomTargetUnitCapTriangleDiagram_last_bridge R C D E p q X Y)
    (dgGluingHomTargetUnitCapTriangleDiagram_coefficient_first R C D E p q X Y)
    (dgGluingHomTargetUnitCapTriangleDiagram_coefficient_last R C D E p q X Y)
end SerrePositivity.InfinityCategories

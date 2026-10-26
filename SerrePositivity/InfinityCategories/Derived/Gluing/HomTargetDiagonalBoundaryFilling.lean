module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitSpanHexagonReduction
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitLoopNullity
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapCoefficientFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitSpanTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitSpanRelativeComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleDiagrams
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCollarIntervalTriangle
/-!
概要：元の六片と二単位閉路を消去し、指定対角三辺の境界を充填する。
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

lemma dgGluingHomTargetUnitCapCoefficientEdge_class :
    Truncated.HomotopyCategory.homMk (dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y) =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)) :=
  dgGluingHomTargetAugmentationDiagonalHomotopy_class R C D E p q X Y

lemma dgGluingHomTargetDiagonalComparisonBoundary_filling_of_actual_coefficient_comp
    (h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y))) :
    ∃ V, (boundary 2).ι ≫ V = dgGluingHomTargetDiagonalComparisonBoundary R C D E p q X Y := by
  rw [dgGluingHomTargetUnitCapCoefficientEdge_class R C D E p q X Y] at h
  exact dgGluingHomotopyTriangleFilling_of_homEq h
def dgGluingHomTargetFirstCollarDiagonalSpanIso :=
  functorIsoOfSimplicialHomotopy (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)

def dgGluingHomTargetLastCapDiagonalSpanIso :=
  functorIsoOfSimplicialHomotopy (dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y)

def dgGluingHomTargetUnitCapCoefficientIso :=
  functorIsoOfSimplicialHomotopy (dgGluingHomTargetAugmentationDiagonalHomotopy R C D E p q X Y)

lemma dgGluingHomTargetDiagonalComparisonBoundary_filling_of_actual_unit_hexagon
    (hhex : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y)) ≫
      (dgGluingHomTargetUnitCapCoefficientIso R C D E p q X Y).inv ≫
        (dgGluingHomTargetLastCapDiagonalSpanIso R C D E p q X Y).hom =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y))) :
    ∃ V, (boundary 2).ι ≫ V = dgGluingHomTargetDiagonalComparisonBoundary R C D E p q X Y := by
  apply dgGluingHomTargetDiagonalComparisonBoundary_filling_of_actual_coefficient_comp
    R C D E p q X Y
  exact dgGluingUnitHexagon_cancel
    (dgGluingHomTargetFirstCollarDiagonalSpanIso R C D E p q X Y)
    (dgGluingHomTargetUnitCapCoefficientIso R C D E p q X Y)
    (dgGluingHomTargetLastCapDiagonalSpanIso R C D E p q X Y)
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y)))
    (dgGluingHomTargetFirstUnitSpanAlignedDiagonalTriangle_homMk_comp R C D E p q X Y)
    (dgGluingHomTargetLastUnitSpanAlignedDiagonalTriangle_homMk_comp R C D E p q X Y)
    (dgGluingHomTargetUnitCollarCompositionTriangle_homMk_comp R C D E p q X Y) hhex
lemma dgGluingHomTargetUnitSixTriangle_first_cap_edge :
    (dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 0 2 =
      functorEdgeOfSimplicialHomotopy (dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y) := by
  apply Truncated.Edge.ext
  exact congrArg SSet.yonedaEquiv
    (dgGluingHomTargetUnitCapTriangleDiagram_first_cap R C D E p q X Y)

lemma dgGluingHomTargetUnitSixTriangle_last_cap_edge :
    (dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 2 0 =
      functorEdgeOfSimplicialHomotopy (dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y) := by
  apply Truncated.Edge.ext
  exact congrArg SSet.yonedaEquiv
    (dgGluingHomTargetUnitCapTriangleDiagram_last_cap R C D E p q X Y)

lemma dgGluingHomTargetUnitSixTriangle_coefficient_edge :
    (dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 4 1 =
      dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y := by
  apply Truncated.Edge.ext
  exact (dgGluingHomTargetUnitCapCoefficientEdge_edge R C D E p q X Y).symm

lemma dgGluingHomTargetUnitSixTriangle_bridge_edge :
    (dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 5 1 =
      functorEdgeOfSimplicialHomotopy (dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y) := by
  apply Truncated.Edge.ext
  change SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫
    dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 5) = _
  rw [dgGluingHomTargetUnitCapTriangleDiagram_collar_bridge R C D E p q X Y]
  exact congrArg SSet.yonedaEquiv
    (dgGluingHomTargetUnitCollarCompositionTriangle R C D E p q X Y).face_one

lemma dgGluingHomTargetUnitSixTriangle_coefficient_iso :
    (dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edgeIso 4 1 =
      dgGluingHomTargetUnitCapCoefficientIso R C D E p q X Y := by
  apply Iso.ext
  change Truncated.HomotopyCategory.homMk
      ((dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 4 1) =
    Truncated.HomotopyCategory.homMk (dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y)
  exact congrArg (fun e => Truncated.HomotopyCategory.homMk e)
    (dgGluingHomTargetUnitSixTriangle_coefficient_edge R C D E p q X Y)

lemma dgGluingHomTargetDiagonalComparisonBoundary_filling_of_model_unit_classes
    (hr : Truncated.HomotopyCategory.homMk
      ((dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 0 0) = 𝟙 _)
    (hl : Truncated.HomotopyCategory.homMk
      ((dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 2 2) = 𝟙 _) :
    ∃ V, (boundary 2).ι ≫ V = dgGluingHomTargetDiagonalComparisonBoundary R C D E p q X Y := by
  apply dgGluingHomTargetDiagonalComparisonBoundary_filling_of_actual_unit_hexagon R C D E p q X Y
  exact (dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).hexagon_of_unit_classes_transport
    (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y))
    (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y))
    (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y))
    (dgGluingHomTargetUnitCapCoefficientIso R C D E p q X Y)
    (dgGluingHomTargetUnitSixTriangle_first_cap_edge R C D E p q X Y)
    (dgGluingHomTargetUnitSixTriangle_last_cap_edge R C D E p q X Y)
    (dgGluingHomTargetUnitSixTriangle_bridge_edge R C D E p q X Y)
    (dgGluingHomTargetUnitSixTriangle_coefficient_iso R C D E p q X Y) hr hl
lemma dgGluingHomTargetDiagonalComparisonBoundary_filling :
    ∃ V, (boundary 2).ι ≫ V = dgGluingHomTargetDiagonalComparisonBoundary R C D E p q X Y := by
  apply dgGluingHomTargetDiagonalComparisonBoundary_filling_of_model_unit_classes R C D E p q X Y
  · rw [← dgGluingHomTargetRightUnitLoop_edge R C D E p q X Y]
    exact dgGluingHomTargetRightUnitLoop_class R C D E p q X Y
  · rw [← dgGluingHomTargetLeftUnitLoop_edge R C D E p q X Y]
    exact dgGluingHomTargetLeftUnitLoop_class R C D E p q X Y

end SerrePositivity.InfinityCategories

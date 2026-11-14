module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.UnitSpanHexagonReduction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitLoopNullity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitCapCoefficientFace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitSpanTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomTargetUnitSpanRelativeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomTargetDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitTriangleDiagrams
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitCollarIntervalTriangle
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetUnitCapCoefficientEdge_class :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y) =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationDiagonalHomotopy_class R C D E p q X Y

lemma dgGluingHomTargetDiagonalComparisonBoundary_filling_of_actual_coefficient_comp
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y))) :
    ∃ V, (boundary 2).ι ≫ V = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary R C D E p q X Y := by
  rw [dgGluingHomTargetUnitCapCoefficientEdge_class R C D E p q X Y] at h
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleFilling_of_homEq h
def dgGluingHomTargetFirstCollarDiagonalSpanIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)

def dgGluingHomTargetLastCapDiagonalSpanIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y)

def dgGluingHomTargetUnitCapCoefficientIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationDiagonalHomotopy R C D E p q X Y)

lemma dgGluingHomTargetDiagonalComparisonBoundary_filling_of_actual_unit_hexagon
    (hhex : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y)) ≫
      (dgGluingHomTargetUnitCapCoefficientIso R C D E p q X Y).inv ≫
        (dgGluingHomTargetLastCapDiagonalSpanIso R C D E p q X Y).hom =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y))) :
    ∃ V, (boundary 2).ι ≫ V = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary R C D E p q X Y := by
  apply dgGluingHomTargetDiagonalComparisonBoundary_filling_of_actual_coefficient_comp
    R C D E p q X Y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitHexagon_cancel
    (dgGluingHomTargetFirstCollarDiagonalSpanIso R C D E p q X Y)
    (dgGluingHomTargetUnitCapCoefficientIso R C D E p q X Y)
    (dgGluingHomTargetLastCapDiagonalSpanIso R C D E p q X Y)
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstUnitSpanAlignedDiagonalTriangle_homMk_comp R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastUnitSpanAlignedDiagonalTriangle_homMk_comp R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarCompositionTriangle_homMk_comp R C D E p q X Y) hhex
lemma dgGluingHomTargetUnitSixTriangle_first_cap_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 0 2 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y) := by
  apply Truncated.Edge.ext
  exact congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram_first_cap R C D E p q X Y)

lemma dgGluingHomTargetUnitSixTriangle_last_cap_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 2 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y) := by
  apply Truncated.Edge.ext
  exact congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram_last_cap R C D E p q X Y)

lemma dgGluingHomTargetUnitSixTriangle_coefficient_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 4 1 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y := by
  apply Truncated.Edge.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapCoefficientEdge_edge R C D E p q X Y).symm

lemma dgGluingHomTargetUnitSixTriangle_bridge_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 5 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y) := by
  apply Truncated.Edge.ext
  change SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 5) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram_collar_bridge R C D E p q X Y]
  exact congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarCompositionTriangle R C D E p q X Y).face_one

lemma dgGluingHomTargetUnitSixTriangle_coefficient_iso :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edgeIso 4 1 =
      dgGluingHomTargetUnitCapCoefficientIso R C D E p q X Y := by
  apply Iso.ext
  change Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 4 1) =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapCoefficientEdge R C D E p q X Y)
  exact congrArg (fun e => Truncated.HomotopyCategory.homMk e)
    (dgGluingHomTargetUnitSixTriangle_coefficient_edge R C D E p q X Y)

lemma dgGluingHomTargetDiagonalComparisonBoundary_filling_of_model_unit_classes
    (hr : Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 0 0) = 𝟙 _)
    (hl : Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 2 2) = 𝟙 _) :
    ∃ V, (boundary 2).ι ≫ V = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary R C D E p q X Y := by
  apply dgGluingHomTargetDiagonalComparisonBoundary_filling_of_actual_unit_hexagon R C D E p q X Y
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).hexagon_of_unit_classes_transport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y))
    (dgGluingHomTargetUnitCapCoefficientIso R C D E p q X Y)
    (dgGluingHomTargetUnitSixTriangle_first_cap_edge R C D E p q X Y)
    (dgGluingHomTargetUnitSixTriangle_last_cap_edge R C D E p q X Y)
    (dgGluingHomTargetUnitSixTriangle_bridge_edge R C D E p q X Y)
    (dgGluingHomTargetUnitSixTriangle_coefficient_iso R C D E p q X Y) hr hl
lemma dgGluingHomTargetDiagonalComparisonBoundary_filling :
    ∃ V, (boundary 2).ι ≫ V = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary R C D E p q X Y := by
  apply dgGluingHomTargetDiagonalComparisonBoundary_filling_of_model_unit_classes R C D E p q X Y
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightUnitLoop_edge R C D E p q X Y]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightUnitLoop_class R C D E p q X Y
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftUnitLoop_edge R C D E p q X Y]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftUnitLoop_class R C D E p q X Y

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitSpanTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitSpanRelativeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitTriangleDiagrams
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCollarIntervalTriangle
/-!
概要：元入力固定の相対充填を指定三辺を持つ実合成三角形へ移す。
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

def dgGluingHomTargetFirstUnitSpanTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCollarSpanHomotopy R C D E p q X Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapSpanHomotopy R C D E p q X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangleOfBoundary
    (Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstUnitSpan_relative_filling R C D E p q X Y))
    (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstUnitSpan_relative_filling R C D E p q X Y)).1

lemma dgGluingHomTargetFirstUnitSpan_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCollarSpanHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapSpanHomotopy R C D E p q X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangle_homEq (dgGluingHomTargetFirstUnitSpanTriangle R C D E p q X Y)

def dgGluingHomTargetFirstUnitSpanDiagonalTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTrianglePostcomp (dgGluingHomTargetFirstUnitSpanTriangle R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)

def dgGluingHomTargetLastUnitSpanTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputHomotopy R C D E p q X Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapSpanHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarSpanHomotopy R C D E p q X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangleOfBoundary
    (Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastUnitSpan_relative_filling R C D E p q X Y))
    (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastUnitSpan_relative_filling R C D E p q X Y)).1

lemma dgGluingHomTargetLastUnitSpan_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapSpanHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarSpanHomotopy R C D E p q X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangle_homEq (dgGluingHomTargetLastUnitSpanTriangle R C D E p q X Y)

def dgGluingHomTargetLastUnitSpanDiagonalTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTrianglePostcomp (dgGluingHomTargetLastUnitSpanTriangle R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y)

def dgGluingHomTargetFirstCollarDiagonalSpanHomotopy :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCollarSpanHomotopy R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowInputLift_diagonals R C D E p q X Y).symm

def dgGluingHomTargetLastCollarDiagonalSpanHomotopy :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarSpanHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y)

def dgGluingHomTargetFirstCapDiagonalSpanHomotopy :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapSpanHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)

def dgGluingHomTargetLastCapDiagonalSpanHomotopy :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapSpanHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y)

def dgGluingHomTargetUnitCollarBridgeHomotopy :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorTriangleThirdHomotopy
    (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarTriangleDiagram R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarTriangleDiagram_two R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarTriangleDiagram_zero R C D E p q X Y)

def dgGluingHomTargetUnitCollarCompositionTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorTriangleOfTwoFaces
    (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarTriangleDiagram R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarTriangleDiagram_two R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarTriangleDiagram_zero R C D E p q X Y)

lemma dgGluingHomTargetUnitCollarCompositionTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangle_homEq (dgGluingHomTargetUnitCollarCompositionTriangle R C D E p q X Y)
def dgGluingHomTargetFirstUnitSpanAlignedDiagonalTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)
    (dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y) where
  diagram := (dgGluingHomTargetFirstUnitSpanDiagonalTriangle R C D E p q X Y).diagram
  face_zero := (dgGluingHomTargetFirstUnitSpanDiagonalTriangle R C D E p q X Y).face_zero
  face_one := (dgGluingHomTargetFirstUnitSpanDiagonalTriangle R C D E p q X Y).face_one
  face_two := (dgGluingHomTargetFirstUnitSpanDiagonalTriangle R C D E p q X Y).face_two

def dgGluingHomTargetLastUnitSpanAlignedDiagonalTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y) where
  diagram := (dgGluingHomTargetLastUnitSpanDiagonalTriangle R C D E p q X Y).diagram
  face_zero := (dgGluingHomTargetLastUnitSpanDiagonalTriangle R C D E p q X Y).face_zero
  face_one := (dgGluingHomTargetLastUnitSpanDiagonalTriangle R C D E p q X Y).face_one
  face_two := (dgGluingHomTargetLastUnitSpanDiagonalTriangle R C D E p q X Y).face_two

lemma dgGluingHomTargetFirstUnitSpanAlignedDiagonalTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangle_homEq
    (dgGluingHomTargetFirstUnitSpanAlignedDiagonalTriangle R C D E p q X Y)

lemma dgGluingHomTargetLastUnitSpanAlignedDiagonalTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangle_homEq
    (dgGluingHomTargetLastUnitSpanAlignedDiagonalTriangle R C D E p q X Y)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

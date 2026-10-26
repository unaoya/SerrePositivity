module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitSpanTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitSpanRelativeComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleDiagrams
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCollarIntervalTriangle
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

def dgGluingHomTargetFirstUnitSpanTriangle : FunctorCompositionTriangle
    (dgGluingHomTargetPreCollarSpanHomotopy R C D E p q X Y) (dgGluingHomTargetFirstInputHomotopy R C D E p q X Y)
    (dgGluingHomTargetPreCapSpanHomotopy R C D E p q X Y) :=
  dgGluingFunctorCompositionTriangleOfBoundary
    (Classical.choose (dgGluingHomTargetFirstUnitSpan_relative_filling R C D E p q X Y))
    (Classical.choose_spec (dgGluingHomTargetFirstUnitSpan_relative_filling R C D E p q X Y)).1

lemma dgGluingHomTargetFirstUnitSpan_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetPreCollarSpanHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetFirstInputHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetPreCapSpanHomotopy R C D E p q X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq (dgGluingHomTargetFirstUnitSpanTriangle R C D E p q X Y)

def dgGluingHomTargetFirstUnitSpanDiagonalTriangle :=
  dgGluingFunctorCompositionTrianglePostcomp (dgGluingHomTargetFirstUnitSpanTriangle R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)

def dgGluingHomTargetLastUnitSpanTriangle : FunctorCompositionTriangle
    (dgGluingHomTargetLastInputHomotopy R C D E p q X Y) (dgGluingHomTargetExitCapSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetExitCollarSpanHomotopy R C D E p q X Y) :=
  dgGluingFunctorCompositionTriangleOfBoundary
    (Classical.choose (dgGluingHomTargetLastUnitSpan_relative_filling R C D E p q X Y))
    (Classical.choose_spec (dgGluingHomTargetLastUnitSpan_relative_filling R C D E p q X Y)).1

lemma dgGluingHomTargetLastUnitSpan_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetLastInputHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetExitCapSpanHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingHomTargetExitCollarSpanHomotopy R C D E p q X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq (dgGluingHomTargetLastUnitSpanTriangle R C D E p q X Y)

def dgGluingHomTargetLastUnitSpanDiagonalTriangle :=
  dgGluingFunctorCompositionTrianglePostcomp (dgGluingHomTargetLastUnitSpanTriangle R C D E p q X Y)
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)

def dgGluingHomTargetFirstCollarDiagonalSpanHomotopy :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp (dgGluingHomTargetPreCollarSpanHomotopy R C D E p q X Y)
      (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)) rfl
    (dgGluingHomTargetArrowInputLift_diagonals R C D E p q X Y).symm

def dgGluingHomTargetLastCollarDiagonalSpanHomotopy :=
  functorHomotopyPostcomp (dgGluingHomTargetExitCollarSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)

def dgGluingHomTargetFirstCapDiagonalSpanHomotopy :=
  functorHomotopyPostcomp (dgGluingHomTargetPreCapSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)

def dgGluingHomTargetLastCapDiagonalSpanHomotopy :=
  functorHomotopyPostcomp (dgGluingHomTargetExitCapSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)

def dgGluingHomTargetUnitCollarBridgeHomotopy :=
  dgGluingFunctorTriangleThirdHomotopy
    (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetUnitCollarTriangleDiagram R C D E p q X Y)
    (dgGluingHomTargetUnitCollarTriangleDiagram_two R C D E p q X Y)
    (dgGluingHomTargetUnitCollarTriangleDiagram_zero R C D E p q X Y)

def dgGluingHomTargetUnitCollarCompositionTriangle : FunctorCompositionTriangle
    (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y) :=
  dgGluingFunctorTriangleOfTwoFaces
    (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetUnitCollarTriangleDiagram R C D E p q X Y)
    (dgGluingHomTargetUnitCollarTriangleDiagram_two R C D E p q X Y)
    (dgGluingHomTargetUnitCollarTriangleDiagram_zero R C D E p q X Y)

lemma dgGluingHomTargetUnitCollarCompositionTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetUnitCollarBridgeHomotopy R C D E p q X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq (dgGluingHomTargetUnitCollarCompositionTriangle R C D E p q X Y)
def dgGluingHomTargetFirstUnitSpanAlignedDiagonalTriangle : FunctorCompositionTriangle
    (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)
    (dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y) where
  diagram := (dgGluingHomTargetFirstUnitSpanDiagonalTriangle R C D E p q X Y).diagram
  face_zero := (dgGluingHomTargetFirstUnitSpanDiagonalTriangle R C D E p q X Y).face_zero
  face_one := (dgGluingHomTargetFirstUnitSpanDiagonalTriangle R C D E p q X Y).face_one
  face_two := (dgGluingHomTargetFirstUnitSpanDiagonalTriangle R C D E p q X Y).face_two

def dgGluingHomTargetLastUnitSpanAlignedDiagonalTriangle : FunctorCompositionTriangle
    (dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y) where
  diagram := (dgGluingHomTargetLastUnitSpanDiagonalTriangle R C D E p q X Y).diagram
  face_zero := (dgGluingHomTargetLastUnitSpanDiagonalTriangle R C D E p q X Y).face_zero
  face_one := (dgGluingHomTargetLastUnitSpanDiagonalTriangle R C D E p q X Y).face_one
  face_two := (dgGluingHomTargetLastUnitSpanDiagonalTriangle R C D E p q X Y).face_two

lemma dgGluingHomTargetFirstUnitSpanAlignedDiagonalTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetFirstCollarDiagonalSpanHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetFirstCapDiagonalSpanHomotopy R C D E p q X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq
    (dgGluingHomTargetFirstUnitSpanAlignedDiagonalTriangle R C D E p q X Y)

lemma dgGluingHomTargetLastUnitSpanAlignedDiagonalTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetLastCapDiagonalSpanHomotopy R C D E p q X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomTargetLastCollarDiagonalSpanHomotopy R C D E p q X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq
    (dgGluingHomTargetLastUnitSpanAlignedDiagonalTriangle R C D E p q X Y)
end SerrePositivity.InfinityCategories

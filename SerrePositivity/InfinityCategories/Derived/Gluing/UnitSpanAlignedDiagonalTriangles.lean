module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCollarCompositionTriangle
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCapCoefficientChoiceComparison
/-! # 指定対角辺に端点を合わせた実単位補正三角形

概要：実単位補正三角形を、正本共通対角と正本係数対角を端点とする同じ三角形へ移す。
方針：元入力 lift の対角等式で端点表示だけを合わせ、実三辺と二単体を保持する。
規約：実補正道や指定済み変形の全時間を変更しない。
使われ方：六片の高次合成等式を、正本の三対角辺の合成等式へ消去する。
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

def dgGluingFirstCapDiagonalSpanHomotopy :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp (dgGluingPreCapSpanHomotopy R C D M X Y)
      (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)) rfl
    (dgGluingHomDerivedFirstCompositionInputLift_diagonal R C D M X Y)

def dgGluingLastCapDiagonalSpanHomotopy :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp (dgGluingExitCapSpanHomotopy R C D M X Y)
      (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y))
    (dgGluingHomDerivedLastCompositionInputLift_diagonal R C D M X Y) rfl

def dgGluingFirstUnitSpanAlignedDiagonalTriangle : FunctorCompositionTriangle
    (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y)
    (dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y) where
  diagram := (dgGluingFirstUnitSpanDiagonalTriangle R C D M X Y).diagram
  face_zero := (dgGluingFirstUnitSpanDiagonalTriangle R C D M X Y).face_zero
  face_one := (dgGluingFirstUnitSpanDiagonalTriangle R C D M X Y).face_one
  face_two := (dgGluingFirstUnitSpanDiagonalTriangle R C D M X Y).face_two

def dgGluingLastUnitSpanAlignedDiagonalTriangle : FunctorCompositionTriangle
    (dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)
    (dgGluingLastCapDiagonalSpanHomotopy R C D M X Y)
    (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y) where
  diagram := (dgGluingLastUnitSpanDiagonalTriangle R C D M X Y).diagram
  face_zero := (dgGluingLastUnitSpanDiagonalTriangle R C D M X Y).face_zero
  face_one := (dgGluingLastUnitSpanDiagonalTriangle R C D M X Y).face_one
  face_two := (dgGluingLastUnitSpanDiagonalTriangle R C D M X Y).face_two

lemma dgGluingFirstUnitSpanAlignedDiagonalTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq
    (dgGluingFirstUnitSpanAlignedDiagonalTriangle R C D M X Y)

lemma dgGluingLastUnitSpanAlignedDiagonalTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingLastCapDiagonalSpanHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq
    (dgGluingLastUnitSpanAlignedDiagonalTriangle R C D M X Y)
end SerrePositivity.InfinityCategories

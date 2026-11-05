module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitCollarTriangle
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitSpanTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorTriangleTwoFaces
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomDiagonalDeformations
/-! # 同じ四面体から取り出す左右実補正対角の合成三角形

概要：左右実補正道の対角を、同じ主経路上の実合成三角形へ接続する。
方針：正本の共通対角で端点表示を合わせ、同じ二単体の第三辺を橋として取り出す。
規約：実補正道・全入力・全時間・四面体由来の二単体を保持する。
使われ方：係数面を含む残りの高次貼り合わせを、選択済み二変形へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingFirstCollarDiagonalSpanHomotopy :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp (dgGluingPreCollarSpanHomotopy R C D M X Y)
      (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)) rfl
    (dgGluingLaxHomCommonDiagonal_first R C D M X Y).symm

def dgGluingLastCollarDiagonalSpanHomotopy :=
  functorHomotopyPostcomp (dgGluingExitCollarSpanHomotopy R C D M X Y)
    (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)

def dgGluingUnitCollarBridgeHomotopy :=
  dgGluingFunctorTriangleThirdHomotopy
    (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingModelUnitCollarTriangleDiagram R C D M X Y)
    (dgGluingModelUnitCollarTriangleDiagram_two R C D M X Y)
    (dgGluingModelUnitCollarTriangleDiagram_zero R C D M X Y)

def dgGluingUnitCollarCompositionTriangle : FunctorCompositionTriangle
    (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingUnitCollarBridgeHomotopy R C D M X Y) :=
  dgGluingFunctorTriangleOfTwoFaces
    (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingModelUnitCollarTriangleDiagram R C D M X Y)
    (dgGluingModelUnitCollarTriangleDiagram_two R C D M X Y)
    (dgGluingModelUnitCollarTriangleDiagram_zero R C D M X Y)

lemma dgGluingUnitCollarCompositionTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingUnitCollarBridgeHomotopy R C D M X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq (dgGluingUnitCollarCompositionTriangle R C D M X Y)
end SerrePositivity.InfinityCategories

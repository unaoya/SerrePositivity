module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputPathPoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyTriangleFillingSquare
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitCollarTriangle
/-! # 指定境界充填から正本入力付き path 比較の実ホモトピーへ

概要：指定三辺を保つ充填から、元二入力を持つ正本比較と導来係数比較の間の実ホモトピーを得る。
方針：同じ充填を全 path 正方形へ戻し、F2 の引き戻し内ホモトピーを既存座標同型で輸送する。
規約：充填・指定三辺・元二入力・全円柱を保持し、比較の公開型へ仮定を追加しない。
使われ方：④の充填を⑤の実 Hom 比較の同値性へ接続する。
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
local notation "K" => dgGluingModelUnitCollarParameter R C D M X Y
variable
  (T : (Δ[2] : SSet.{max (u + 1) v w}) ⟶
    (ihom (dgGluingModelUnitCollarParameter R C D M X Y)).obj
    (intervalMappingSpace
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left)))
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right)))))
  (hT : (boundary 2).ι ≫ T = dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y)

def dgGluingLaxHomInputPathSquareOfFilling :
    SSet.Homotopy (dgGluingLaxHomInputPathStartHomotopy R C D M X Y).h
      (dgGluingLaxHomInputPathEndHomotopy R C D M X Y).h :=
  dgGluingBoundaryFillingPathSquare
    (l := dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)
    (r := dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)
    (d := dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y) T hT

lemma dgGluingLaxHomInputPathSquareOfFilling_left :
    ((ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{max (u + 1) v w})) ▷
      (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (dgGluingLaxHomInputPathSquareOfFilling R C D M X Y T hT).h =
    (dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
      dgGluingDerivedLastCompositionInputDiagonal R C D M X Y :=
  dgGluingBoundaryFillingPathSquare_left
    (l := dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)
    (r := dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)
    (d := dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y) T hT

lemma dgGluingLaxHomInputPathSquareOfFilling_right :
    ((ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{max (u + 1) v w})) ▷
      (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (dgGluingLaxHomInputPathSquareOfFilling R C D M X Y T hT).h =
    (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
      dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y :=
  dgGluingBoundaryFillingPathSquare_right
    (l := dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)
    (r := dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)
    (d := dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y) T hT

def dgGluingLaxHomInputPathComparisonHomotopyOfFilling :
    SSet.Homotopy (dgGluingLaxHomInputPathComparison R C D M X Y)
      (dgGluingHomDerivedCompositionInputPathComparison R C D M X Y) :=
  stableHomotopyRetarget
    (dgGluingIntervalPathPullbackHomotopyOfSquare
      (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
      (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)
      (dgGluingLaxHomInputPathStartHomotopy R C D M X Y)
      (dgGluingLaxHomInputPathEndHomotopy R C D M X Y)
      (dgGluingLaxHomLastInputHomotopy R C D M X Y)
      (dgGluingLaxHomFirstInputHomotopy R C D M X Y)
      (dgGluingLaxHomInputPathSquareOfFilling R C D M X Y T hT)
      (dgGluingLaxHomInputPathSquareOfFilling_left R C D M X Y T hT)
      (dgGluingLaxHomInputPathSquareOfFilling_right R C D M X Y T hT))
    (dgGluingLaxHomInputPathStartPoint_eq R C D M X Y)
    (dgGluingLaxHomInputPathEndPoint_eq R C D M X Y)
end SerrePositivity.InfinityCategories

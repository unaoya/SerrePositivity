module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberBoundaryTriangles
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataLowDimensionalPullback

/-! # 標準 fiber の錐から回収した境界データの対象と成分

概要：最後の頂点に標準 fiber の錐を持つ境界データの対象・辺・三点成分を同定する。
方針：最後の三角形のデータの等式を対象と斉次成分で評価する。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：fiber の Hom 座標へ既知の残差を移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：左の境界データの apex に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_left_apex {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) 2 => s.obj (0 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_triangle g h b hb)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h at H
  exact H

/-- 概要：左の境界データの B に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_left_B {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) = B := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) 2 => s.obj (1 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_triangle g h b hb)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) = B at H
  exact H

/-- 概要：左の境界データの D に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_left_D {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) = D := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) 2 => s.obj (2 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_triangle g h b hb)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) = D at H
  exact H

/-- 概要：右の境界データの apex に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_right_apex {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) 2 => s.obj (0 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_right_triangle g h b hb)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h at H
  exact H

/-- 概要：右の境界データの C に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_right_C {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) = C := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) 2 => s.obj (1 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_right_triangle g h b hb)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) = C at H
  exact H

/-- 概要：右の境界データの D に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_right_D {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) = D := by
  have H := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) 2 => s.obj (2 : Fin 3))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_right_triangle g h b hb)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) = D at H
  exact H


/-- 概要：左の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_left_projection_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n))
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_triangle g h b hb)
    (0 : Fin 3) 1 (by decide) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) from rfl))

/-- 概要：左の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_left_cospan_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
      (Cochain.ofHom g) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_triangle g h b hb)
    (1 : Fin 3) 2 (by decide) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      Cochain.ofHom g from rfl))

/-- 概要：左の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_left_diagonal_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)))
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackDiagonal g h)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_triangle g h b hb)
    (0 : Fin 3) 2 (by decide) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackDiagonal g h) from rfl))

/-- 概要：左の境界データの三点成分は標準 fiber の錐の指定したホモトピー。
方針：最後の三角形への単射の制限の等式を三点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の高次成分との合成を標準 fiber のホモトピーで書く。 -/
lemma fiberSliceBoundary_left_homotopy_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).tripleHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_triangle g h b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).simplex.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h) from rfl))

/-- 概要：右の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_right_projection_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n))
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_right_triangle g h b hb)
    (0 : Fin 3) 1 (by decide) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h) from rfl))

/-- 概要：右の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_right_cospan_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
      (Cochain.ofHom h) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_right_triangle g h b hb)
    (1 : Fin 3) 2 (by decide) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      Cochain.ofHom h from rfl))

/-- 概要：右の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_right_diagonal_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).edgeHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)))
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackDiagonal g h)) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_right_triangle g h b hb)
    (0 : Fin 3) 2 (by decide) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackDiagonal g h) from rfl))

/-- 概要：右の境界データの三点成分は標準 fiber の錐の指定したホモトピー。
方針：最後の三角形への単射の制限の等式を三点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の高次成分との合成を標準 fiber のホモトピーで書く。 -/
lemma fiberSliceBoundary_right_homotopy_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).tripleHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
      ((0 : Cochain (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) D (-1))) := by
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom_injective (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_right_triangle g h b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)
  exact H.trans (heq_of_eq (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).simplex.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) =
      (0 : Cochain (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) D (-1)) from rfl))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

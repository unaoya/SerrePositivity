module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryTriangles
public import SerrePositivity.InfinityCategories.DGNerve.DataLowDimensionalPullback

/-! # 標準 fiber の錐から回収した境界データの対象と成分

概要：最後の頂点に標準 fiber の錐を持つ境界データの対象・辺・三点成分を同定する。
方針：最後の三角形のデータの等式を対象と斉次成分で評価する。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：fiber の Hom 座標へ既知の残差を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：左の境界データの apex に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_left_apex {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (cospanBoundaryLeftZeroData (sliceOverUncurry b)).obj (cospanApex n) = pullbackFiber g h := by
  have H := congrArg (fun s : SimplexData A (Complex A) 2 => s.obj (0 : Fin 3))
    (fiberSliceBoundary_left_triangle g h b hb)
  change (cospanBoundaryLeftZeroData (sliceOverUncurry b)).obj (cospanApex n) =
    pullbackFiber g h at H
  exact H

/-- 概要：左の境界データの B に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_left_B {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (cospanBoundaryLeftZeroData (sliceOverUncurry b)).obj (cospanFirstTail n) = B := by
  have H := congrArg (fun s : SimplexData A (Complex A) 2 => s.obj (1 : Fin 3))
    (fiberSliceBoundary_left_triangle g h b hb)
  change (cospanBoundaryLeftZeroData (sliceOverUncurry b)).obj (cospanFirstTail n) = B at H
  exact H

/-- 概要：左の境界データの D に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_left_D {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (cospanBoundaryLeftZeroData (sliceOverUncurry b)).obj (cospanLastTail n) = D := by
  have H := congrArg (fun s : SimplexData A (Complex A) 2 => s.obj (2 : Fin 3))
    (fiberSliceBoundary_left_triangle g h b hb)
  change (cospanBoundaryLeftZeroData (sliceOverUncurry b)).obj (cospanLastTail n) = D at H
  exact H

/-- 概要：右の境界データの apex に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_right_apex {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (cospanBoundaryRightZeroData (sliceOverUncurry b)).obj (cospanApex n) = pullbackFiber g h := by
  have H := congrArg (fun s : SimplexData A (Complex A) 2 => s.obj (0 : Fin 3))
    (fiberSliceBoundary_right_triangle g h b hb)
  change (cospanBoundaryRightZeroData (sliceOverUncurry b)).obj (cospanApex n) =
    pullbackFiber g h at H
  exact H

/-- 概要：右の境界データの C に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_right_C {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (cospanBoundaryRightZeroData (sliceOverUncurry b)).obj (cospanFirstTail n) = C := by
  have H := congrArg (fun s : SimplexData A (Complex A) 2 => s.obj (1 : Fin 3))
    (fiberSliceBoundary_right_triangle g h b hb)
  change (cospanBoundaryRightZeroData (sliceOverUncurry b)).obj (cospanFirstTail n) = C at H
  exact H

/-- 概要：右の境界データの D に対応する対象は標準 fiber の錐の指定対象。
方針：最後の三角形のデータの等式を対応する頂点で評価する。
規約：HTT §1.2.13。使われ方：回収した残差の端点を標準 fiber の対象へ移す。 -/
lemma fiberSliceBoundary_right_D {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (cospanBoundaryRightZeroData (sliceOverUncurry b)).obj (cospanLastTail n) = D := by
  have H := congrArg (fun s : SimplexData A (Complex A) 2 => s.obj (2 : Fin 3))
    (fiberSliceBoundary_right_triangle g h b hb)
  change (cospanBoundaryRightZeroData (sliceOverUncurry b)).obj (cospanLastTail n) = D at H
  exact H


/-- 概要：左の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_left_projection_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((cospanBoundaryLeftZeroData (sliceOverUncurry b)).edgeHom
      (cospanApex n) (cospanFirstTail n) (cospanApex_lt_firstTail n))
      (Cochain.ofHom (pullbackProjectionB g h)) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (fiberSliceBoundary_left_triangle g h b hb)
    (0 : Fin 3) 1 (by decide) (cospanApex_lt_firstTail n)
  exact H.trans (heq_of_eq (show
    (fiberLowerTriangle g h).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      Cochain.ofHom (pullbackProjectionB g h) from rfl))

/-- 概要：左の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_left_cospan_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((cospanBoundaryLeftZeroData (sliceOverUncurry b)).edgeHom
      (cospanFirstTail n) (cospanLastTail n) (cospanFirstTail_lt_lastTail n))
      (Cochain.ofHom g) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (fiberSliceBoundary_left_triangle g h b hb)
    (1 : Fin 3) 2 (by decide) (cospanFirstTail_lt_lastTail n)
  exact H.trans (heq_of_eq (show
    (fiberLowerTriangle g h).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      Cochain.ofHom g from rfl))

/-- 概要：左の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_left_diagonal_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((cospanBoundaryLeftZeroData (sliceOverUncurry b)).edgeHom
      (cospanApex n) (cospanLastTail n)
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)))
      (Cochain.ofHom (pullbackDiagonal g h)) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (fiberSliceBoundary_left_triangle g h b hb)
    (0 : Fin 3) 2 (by decide) ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
  exact H.trans (heq_of_eq (show
    (fiberLowerTriangle g h).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      Cochain.ofHom (pullbackDiagonal g h) from rfl))

/-- 概要：左の境界データの三点成分は標準 fiber の錐の指定したホモトピー。
方針：最後の三角形への単射の制限の等式を三点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の高次成分との合成を標準 fiber のホモトピーで書く。 -/
lemma fiberSliceBoundary_left_homotopy_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((cospanBoundaryLeftZeroData (sliceOverUncurry b)).tripleHom
      (cospanApex n) (cospanFirstTail n) (cospanLastTail n)
      (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
      (fiberNullHomotopy (fiberDifference g h)) := by
  have H := SimplexData.tripleHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (fiberSliceBoundary_left_triangle g h b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n)
  exact H.trans (heq_of_eq (show
    (fiberLowerTriangle g h).simplex.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) =
      fiberNullHomotopy (fiberDifference g h) from rfl))

/-- 概要：右の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_right_projection_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((cospanBoundaryRightZeroData (sliceOverUncurry b)).edgeHom
      (cospanApex n) (cospanFirstTail n) (cospanApex_lt_firstTail n))
      (Cochain.ofHom (pullbackProjectionC g h)) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (fiberSliceBoundary_right_triangle g h b hb)
    (0 : Fin 3) 1 (by decide) (cospanApex_lt_firstTail n)
  exact H.trans (heq_of_eq (show
    (fiberUpperTriangle g h).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      Cochain.ofHom (pullbackProjectionC g h) from rfl))

/-- 概要：右の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_right_cospan_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((cospanBoundaryRightZeroData (sliceOverUncurry b)).edgeHom
      (cospanFirstTail n) (cospanLastTail n) (cospanFirstTail_lt_lastTail n))
      (Cochain.ofHom h) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (fiberSliceBoundary_right_triangle g h b hb)
    (1 : Fin 3) 2 (by decide) (cospanFirstTail_lt_lastTail n)
  exact H.trans (heq_of_eq (show
    (fiberUpperTriangle g h).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      Cochain.ofHom h from rfl))

/-- 概要：右の境界データから回収した辺の成分は標準 fiber の錐の指定した chain map の cochain。
方針：最後の三角形への単射の制限の等式を二点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の脚との合成を標準 fiber の射で書く。 -/
lemma fiberSliceBoundary_right_diagonal_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((cospanBoundaryRightZeroData (sliceOverUncurry b)).edgeHom
      (cospanApex n) (cospanLastTail n)
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)))
      (Cochain.ofHom (pullbackDiagonal g h)) := by
  have H := SimplexData.edgeHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (fiberSliceBoundary_right_triangle g h b hb)
    (0 : Fin 3) 2 (by decide) ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
  exact H.trans (heq_of_eq (show
    (fiberUpperTriangle g h).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      Cochain.ofHom (pullbackDiagonal g h) from rfl))

/-- 概要：右の境界データの三点成分は標準 fiber の錐の指定したホモトピー。
方針：最後の三角形への単射の制限の等式を三点成分で評価する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：残差の高次成分との合成を標準 fiber のホモトピーで書く。 -/
lemma fiberSliceBoundary_right_homotopy_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((cospanBoundaryRightZeroData (sliceOverUncurry b)).tripleHom
      (cospanApex n) (cospanFirstTail n) (cospanLastTail n)
      (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
      ((0 : Cochain (pullbackFiber g h) D (-1))) := by
  have H := SimplexData.tripleHom_heq_of_pullback_eq _ _ (lastTriangleOrderHom (n + 1))
    (lastTriangleOrderHom_injective (n + 1)) (fiberSliceBoundary_right_triangle g h b hb)
    (0 : Fin 3) 1 2 (by decide) (by decide)
    (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n)
  exact H.trans (heq_of_eq (show
    (fiberUpperTriangle g h).simplex.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) =
      (0 : Cochain (pullbackFiber g h) D (-1)) from rfl))

end SerrePositivity.InfinityCategories.DGNerve

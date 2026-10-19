module
public import SerrePositivity.InfinityCategories.Derived.BoundaryFirstTriangles
public import SerrePositivity.InfinityCategories.Derived.SpanBoundaryZeroData

/-! # 最初の三角形への境界データの制限

概要：左右の零未知境界データの最初の三頂点は、境界の最初の頂点の余錐の三角形を回収する。
方針：最初の三頂点を既知の最後の面で回収し、境界への持ち上げの公式を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：標準 fiber の対象・脚・ホモトピーの同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左の零未知データの最初の三角形は、境界の最初の頂点の余錐の左三角形。
方針：最後の面の値を引き戻し、最初の三角形と境界頂点の join の公式で比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：左の標準余錐の三つの対象と全成分の回収。 -/
lemma spanBoundaryLeftZeroData_first_triangle {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    (spanBoundaryLeftZeroData F).pullback (firstTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (spanCoconeTriangleLeft ≫
        joinMap (𝟙 (SSet.horn 2 0 : SSet)) (boundaryVertex n 0) ≫ F)).toSimplexData := by
  have h0 : Fin.last (n + 3) ∈ spanSuffixFaces n :=
    (mem_spanSuffixFaces _).mpr (by change 2 ≤ n + 3; omega)
  calc
    (spanBoundaryLeftZeroData F).pullback (firstTriangleOrderHom (n + 1)) =
        ((spanBoundaryLeftZeroData F).pullback
          (Fin.last (n + 3)).succAboveOrderEmb.toOrderHom).pullback
            (firstTriangleOrderHom n) := by
      rw [SimplexData.pullback_comp, firstTriangleOrderHom_face_last]
    _ = (SSet.yonedaEquiv (spanBoundaryLeftLift n (Fin.last (n + 3)) h0 ≫ F)).toSimplexData.pullback
        (firstTriangleOrderHom n) := by
      rw [spanBoundaryLeftZeroData, spanBoundaryLeftData_pullback_face F _ (Fin.last (n + 3)) h0]
    _ = (SSet.yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.mkHom (firstTriangleOrderHom n)) ≫
        (spanBoundaryLeftLift n (Fin.last (n + 3)) h0 ≫ F))).toSimplexData := by
      change ((dgNerve A D).map (SimplexCategory.mkHom (firstTriangleOrderHom n)).op
        (SSet.yonedaEquiv (spanBoundaryLeftLift n (Fin.last (n + 3)) h0 ≫ F))).toSimplexData = _
      exact congrArg Simplex.toSimplexData (SSet.yonedaEquiv_naturality
        (SimplexCategory.mkHom (firstTriangleOrderHom n))
        (spanBoundaryLeftLift n (Fin.last (n + 3)) h0 ≫ F))
    _ = _ := by
      rw [← Category.assoc, spanBoundaryLeftLift_first_triangle, Category.assoc]

/-- 概要：右の零未知データの最初の三角形は、境界の最初の頂点の余錐の右三角形。
方針：最後の面の値を引き戻し、最初の三角形と境界頂点の join の公式で比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：右の標準余錐の三つの対象と全成分の回収。 -/
lemma spanBoundaryRightZeroData_first_triangle {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    (spanBoundaryRightZeroData F).pullback (firstTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (spanCoconeTriangleRight ≫
        joinMap (𝟙 (SSet.horn 2 0 : SSet)) (boundaryVertex n 0) ≫ F)).toSimplexData := by
  have h0 : Fin.last (n + 3) ∈ spanSuffixFaces n :=
    (mem_spanSuffixFaces _).mpr (by change 2 ≤ n + 3; omega)
  calc
    (spanBoundaryRightZeroData F).pullback (firstTriangleOrderHom (n + 1)) =
        ((spanBoundaryRightZeroData F).pullback
          (Fin.last (n + 3)).succAboveOrderEmb.toOrderHom).pullback
            (firstTriangleOrderHom n) := by
      rw [SimplexData.pullback_comp, firstTriangleOrderHom_face_last]
    _ = (SSet.yonedaEquiv
        (spanBoundaryRightLift n (Fin.last (n + 3)) h0 ≫ F)).toSimplexData.pullback
        (firstTriangleOrderHom n) := by
      rw [spanBoundaryRightZeroData, spanBoundaryRightData_pullback_face F _ (Fin.last (n + 3)) h0]
    _ = (SSet.yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.mkHom (firstTriangleOrderHom n)) ≫
        (spanBoundaryRightLift n (Fin.last (n + 3)) h0 ≫ F))).toSimplexData := by
      change ((dgNerve A D).map (SimplexCategory.mkHom (firstTriangleOrderHom n)).op
        (SSet.yonedaEquiv (spanBoundaryRightLift n (Fin.last (n + 3)) h0 ≫ F))).toSimplexData = _
      exact congrArg Simplex.toSimplexData (SSet.yonedaEquiv_naturality
        (SimplexCategory.mkHom (firstTriangleOrderHom n))
        (spanBoundaryRightLift n (Fin.last (n + 3)) h0 ≫ F))
    _ = _ := by
      rw [← Category.assoc, spanBoundaryRightLift_first_triangle, Category.assoc]

end SerrePositivity.InfinityCategories

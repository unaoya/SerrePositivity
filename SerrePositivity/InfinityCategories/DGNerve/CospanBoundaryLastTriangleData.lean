module
public import SerrePositivity.InfinityCategories.DGNerve.BoundaryLastTriangles
public import SerrePositivity.InfinityCategories.DGNerve.CospanBoundaryZeroData

/-! # 最後の三角形への境界データの制限

概要：左右の零未知境界データの最後の三頂点は、境界の最後の頂点の錐の三角形を回収する。
方針：最後の三頂点を既知の零番目の面で回収し、境界への持ち上げの公式を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：標準 fiber の対象・脚・ホモトピーの同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左の零未知データの最後の三角形は、境界の最後の頂点の錐の左三角形。
方針：零番目の面の値を引き戻し、最後の三角形と境界頂点の join の公式で比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：左の標準錐の三つの対象と全成分の回収。 -/
lemma cospanBoundaryLeftZeroData_last_triangle {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D) :
    (cospanBoundaryLeftZeroData F).pullback (lastTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (cospanConeTriangleLeft ≫
        joinMap (boundaryVertex n (Fin.last (n + 1)))
          (𝟙 (SSet.horn 2 2 : SSet)) ≫ F)).toSimplexData := by
  have h0 : (0 : Fin (n + 4)) ∈ cospanPrefixFaces n :=
    (mem_cospanPrefixFaces _).mpr (by simp)
  calc
    (cospanBoundaryLeftZeroData F).pullback (lastTriangleOrderHom (n + 1)) =
        ((cospanBoundaryLeftZeroData F).pullback
          (0 : Fin (n + 4)).succAboveOrderEmb.toOrderHom).pullback (lastTriangleOrderHom n) := by
      rw [SimplexData.pullback_comp, lastTriangleOrderHom_face_zero]
    _ = (SSet.yonedaEquiv (cospanBoundaryLeftLift n 0 h0 ≫ F)).toSimplexData.pullback
        (lastTriangleOrderHom n) := by
      rw [cospanBoundaryLeftZeroData, cospanBoundaryLeftData_pullback_face F _ 0 h0]
    _ = (SSet.yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.mkHom (lastTriangleOrderHom n)) ≫
        (cospanBoundaryLeftLift n 0 h0 ≫ F))).toSimplexData := by
      change ((dgNerve A D).map (SimplexCategory.mkHom (lastTriangleOrderHom n)).op
        (SSet.yonedaEquiv (cospanBoundaryLeftLift n 0 h0 ≫ F))).toSimplexData = _
      exact congrArg Simplex.toSimplexData (SSet.yonedaEquiv_naturality
        (SimplexCategory.mkHom (lastTriangleOrderHom n)) (cospanBoundaryLeftLift n 0 h0 ≫ F))
    _ = _ := by
      rw [← Category.assoc, cospanBoundaryLeftLift_last_triangle, Category.assoc]

/-- 概要：右の零未知データの最後の三角形は、境界の最後の頂点の錐の右三角形。
方針：零番目の面の値を引き戻し、最後の三角形と境界頂点の join の公式で比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：右の標準錐の三つの対象と全成分の回収。 -/
lemma cospanBoundaryRightZeroData_last_triangle {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D) :
    (cospanBoundaryRightZeroData F).pullback (lastTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (cospanConeTriangleRight ≫
        joinMap (boundaryVertex n (Fin.last (n + 1)))
          (𝟙 (SSet.horn 2 2 : SSet)) ≫ F)).toSimplexData := by
  have h0 : (0 : Fin (n + 4)) ∈ cospanPrefixFaces n :=
    (mem_cospanPrefixFaces _).mpr (by simp)
  calc
    (cospanBoundaryRightZeroData F).pullback (lastTriangleOrderHom (n + 1)) =
        ((cospanBoundaryRightZeroData F).pullback
          (0 : Fin (n + 4)).succAboveOrderEmb.toOrderHom).pullback (lastTriangleOrderHom n) := by
      rw [SimplexData.pullback_comp, lastTriangleOrderHom_face_zero]
    _ = (SSet.yonedaEquiv (cospanBoundaryRightLift n 0 h0 ≫ F)).toSimplexData.pullback
        (lastTriangleOrderHom n) := by
      rw [cospanBoundaryRightZeroData, cospanBoundaryRightData_pullback_face F _ 0 h0]
    _ = (SSet.yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.mkHom (lastTriangleOrderHom n)) ≫
        (cospanBoundaryRightLift n 0 h0 ≫ F))).toSimplexData := by
      change ((dgNerve A D).map (SimplexCategory.mkHom (lastTriangleOrderHom n)).op
        (SSet.yonedaEquiv (cospanBoundaryRightLift n 0 h0 ≫ F))).toSimplexData = _
      exact congrArg Simplex.toSimplexData (SSet.yonedaEquiv_naturality
        (SimplexCategory.mkHom (lastTriangleOrderHom n)) (cospanBoundaryRightLift n 0 h0 ≫ F))
    _ = _ := by
      rw [← Category.assoc, cospanBoundaryRightLift_last_triangle, Category.assoc]

end SerrePositivity.InfinityCategories.DGNerve

module
public import SerrePositivity.InfinityCategories.DGNerve.SliceBoundaryLastCone
public import SerrePositivity.InfinityCategories.DGNerve.CospanBoundaryLastTriangleData

/-! # 指定された錐の三角形のデータの回収

概要：slice 境界の最後の頂点の錐を、左右の境界データの最後の三角形で回収する。
方針：join 境界の最後の三角形の公式に、最後の頂点の錐の回収を代入する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：標準 fiber の対象・脚・高次成分の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：slice 境界の左データの最後の三角形は指定された錐の左三角形のデータ。
方針：最後の三角形の制限を計算し、slice の最後の頂点の条件で錐に置き換える。
規約：HTT §1.2.13。使われ方：標準 fiber の p,g,t,u の回収。 -/
lemma sliceBoundaryLeftData_last_triangle {n : ℕ}
    {p : (SSet.horn 2 2 : SSet.{max u v}) ⟶ dgNerve A D}
    (b : (SSet.boundary (n + 1) : SSet) ⟶ sliceOver p) (c : JoinCone p)
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b = SSet.yonedaEquiv.symm c) :
    (cospanBoundaryLeftZeroData (sliceOverUncurry b)).pullback (lastTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (cospanConeTriangleLeft ≫ c.val)).toSimplexData := by
  rw [cospanBoundaryLeftZeroData_last_triangle, sliceBoundary_last_cone b c hb]

/-- 概要：slice 境界の右データの最後の三角形は指定された錐の右三角形のデータ。
方針：最後の三角形の制限を計算し、slice の最後の頂点の条件で錐に置き換える。
規約：HTT §1.2.13。使われ方：標準 fiber の q,h,t,v の回収。 -/
lemma sliceBoundaryRightData_last_triangle {n : ℕ}
    {p : (SSet.horn 2 2 : SSet.{max u v}) ⟶ dgNerve A D}
    (b : (SSet.boundary (n + 1) : SSet) ⟶ sliceOver p) (c : JoinCone p)
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b = SSet.yonedaEquiv.symm c) :
    (cospanBoundaryRightZeroData (sliceOverUncurry b)).pullback (lastTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (cospanConeTriangleRight ≫ c.val)).toSimplexData := by
  rw [cospanBoundaryRightZeroData_last_triangle, sliceBoundary_last_cone b c hb]

end SerrePositivity.InfinityCategories.DGNerve

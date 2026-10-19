module
public import SerrePositivity.InfinityCategories.Derived.CosliceBoundaryFromJoinFaces
public import SerrePositivity.InfinityCategories.Derived.SpanBoundaryFirstTriangleData

/-! # 指定された余錐の三角形のデータの回収

概要：coslice 境界の最初の頂点の余錐を、左右の境界データの最初の三角形で回収する。
方針：join 境界の最初の三角形の公式に、最初の頂点の余錐の回収を代入する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：標準 cofiber の対象・脚・高次成分の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：coslice 境界の左データの最初の三角形は指定された余錐の左三角形のデータ。
方針：最初の三角形の制限を計算し、coslice の最初の頂点の条件で余錐に置き換える。
規約：HTT §1.2.13。使われ方：標準 cofiber の f,i_B,t,u の回収。 -/
lemma cosliceBoundaryLeftData_first_triangle {n : ℕ}
    {p : (SSet.horn 2 0 : SSet.{max u v}) ⟶ dgNerve A D}
    (b : (SSet.boundary (n + 1) : SSet) ⟶ sliceUnder p) (c : JoinCocone p)
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm c) :
    (spanBoundaryLeftZeroData (sliceUnderUncurry b)).pullback (firstTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (spanCoconeTriangleLeft ≫ c.val)).toSimplexData := by
  rw [spanBoundaryLeftZeroData_first_triangle, cosliceBoundary_first_cocone b c hb]

/-- 概要：coslice 境界の右データの最初の三角形は指定された余錐の右三角形のデータ。
方針：最初の三角形の制限を計算し、coslice の最初の頂点の条件で余錐に置き換える。
規約：HTT §1.2.13。使われ方：標準 cofiber の g,i_C,t,v の回収。 -/
lemma cosliceBoundaryRightData_first_triangle {n : ℕ}
    {p : (SSet.horn 2 0 : SSet.{max u v}) ⟶ dgNerve A D}
    (b : (SSet.boundary (n + 1) : SSet) ⟶ sliceUnder p) (c : JoinCocone p)
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm c) :
    (spanBoundaryRightZeroData (sliceUnderUncurry b)).pullback (firstTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (spanCoconeTriangleRight ≫ c.val)).toSimplexData := by
  rw [spanBoundaryRightZeroData_first_triangle, cosliceBoundary_first_cocone b c hb]

end SerrePositivity.InfinityCategories

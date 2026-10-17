module
public import SerrePositivity.InfinityCategories.DGNerve.SliceBoundaryTriangleData
public import SerrePositivity.InfinityCategories.DGNerve.FiberConeVertex
public import SerrePositivity.InfinityCategories.DGNerve.ComplexTriangleComponents

/-! # 標準 fiber の錐の三角形と境界データ

概要：標準 fiber の錐を最後の頂点に持つ slice 境界から、その錐の二三角形を回収する。
方針：正方形と join 錐の比較、標準四角形の三角形の計算、最後の三頂点の回収を合成する。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：fiber の Hom 座標に渡す対象・射の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：標準 fiber の錐の左三角形は指定された B を通る合成三角形。
方針：join と正方形の比較の左三角形と標準四角形の下側三角形を使う。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：左の p,g,t,u の指定。 -/
lemma standardFiberCone_left_triangle (g : B ⟶ D) (h : C ⟶ D) :
    cospanConeTriangleLeft ≫ (standardFiberCone g h).val =
      SSet.yonedaEquiv.symm (fiberLowerTriangle g h).simplex := by
  change cospanConeTriangleLeft ≫ (cospanConeSquareIso.hom ≫ standardFiberSquare g h) = _
  rw [← Category.assoc, cospanConeSquareIso_left, standardFiberSquare_lower]

/-- 概要：標準 fiber の錐の右三角形は指定された C を通る合成三角形。
方針：join と正方形の比較の右三角形と標準四角形の上側三角形を使う。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：右の q,h,t,v の指定。 -/
lemma standardFiberCone_right_triangle (g : B ⟶ D) (h : C ⟶ D) :
    cospanConeTriangleRight ≫ (standardFiberCone g h).val =
      SSet.yonedaEquiv.symm (fiberUpperTriangle g h).simplex := by
  change cospanConeTriangleRight ≫ (cospanConeSquareIso.hom ≫ standardFiberSquare g h) = _
  rw [← Category.assoc, cospanConeSquareIso_right, standardFiberSquare_upper]

/-- 概要：標準 fiber の錐を終点に持つ境界の左データは最後の三角形で標準下側三角形に等しい。
方針：最後の錐の左三角形の回収と標準 fiber の錐の三角形の計算を合成する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：左の三つの対象と p,g,t,u の回収。 -/
lemma fiberSliceBoundary_left_triangle {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (cospanBoundaryLeftZeroData (sliceOverUncurry b)).pullback (lastTriangleOrderHom (n + 1)) =
      (fiberLowerTriangle g h).simplex.toSimplexData := by
  rw [sliceBoundaryLeftData_last_triangle b (standardFiberCone g h) hb,
    standardFiberCone_left_triangle, Equiv.apply_symm_apply]

/-- 概要：標準 fiber の錐を終点に持つ境界の右データは最後の三角形で標準上側三角形に等しい。
方針：最後の錐の右三角形の回収と標準 fiber の錐の三角形の計算を合成する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：右の三つの対象と q,h,t,v の回収。 -/
lemma fiberSliceBoundary_right_triangle {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (cospanBoundaryRightZeroData (sliceOverUncurry b)).pullback (lastTriangleOrderHom (n + 1)) =
      (fiberUpperTriangle g h).simplex.toSimplexData := by
  rw [sliceBoundaryRightData_last_triangle b (standardFiberCone g h) hb,
    standardFiberCone_right_triangle, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.DGNerve

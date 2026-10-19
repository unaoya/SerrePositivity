module
public import SerrePositivity.InfinityCategories.Derived.CosliceBoundaryTriangleData
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeSquare

/-! # 標準 cofiber の余錐の三角形と境界データ

概要：標準 cofiber の余錐を最初の頂点に持つ coslice 境界から、その余錐の二三角形を回収する。
方針：正方形と join 余錐の比較、標準四角形の三角形の計算、最初の三頂点の回収を合成する。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：cofiber の Hom 座標に渡す対象・射の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：標準 cofiber の余錐の左三角形は指定された B を通る合成三角形。
方針：join と正方形の比較の左三角形と標準四角形の下側三角形を使う。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：左の f,i_B,t,u の指定。 -/
lemma dgModuleConeCocone_left_triangle (f : M ⟶ N) :
    spanCoconeTriangleLeft ≫ (dgModuleConeCocone A D f).val =
      SSet.yonedaEquiv.symm (dgModuleConeLowerTriangle A D f).simplex := by
  change spanCoconeTriangleLeft ≫ (spanCoconeSquareIso.hom ≫ dgModuleConeSquare A D f) = _
  rw [← Category.assoc, spanCoconeSquareIso_left, dgModuleConeSquare_lower]

/-- 概要：標準 cofiber の余錐の右三角形は指定された C を通る合成三角形。
方針：join と正方形の比較の右三角形と標準四角形の上側三角形を使う。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：右の g,i_C,t,v の指定。 -/
lemma dgModuleConeCocone_right_triangle (f : M ⟶ N) :
    spanCoconeTriangleRight ≫ (dgModuleConeCocone A D f).val =
      SSet.yonedaEquiv.symm (dgModuleConeUpperTriangle A D f).simplex := by
  change spanCoconeTriangleRight ≫ (spanCoconeSquareIso.hom ≫ dgModuleConeSquare A D f) = _
  rw [← Category.assoc, spanCoconeSquareIso_right, dgModuleConeSquare_upper]

/-- 概要：標準 cofiber の余錐を始点に持つ境界の左データは最初の三角形で標準下側三角形に等しい。
方針：最初の余錐の左三角形の回収と標準 cofiber の余錐の三角形の計算を合成する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：左の三つの対象と f,i_B,t,u の回収。 -/
lemma dgModuleConeBoundary_left_triangle {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b =
      SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (spanBoundaryLeftZeroData (sliceUnderUncurry b)).pullback (firstTriangleOrderHom (n + 1)) =
      (dgModuleConeLowerTriangle A D f).simplex.toSimplexData := by
  rw [cosliceBoundaryLeftData_first_triangle b (dgModuleConeCocone A D f) hb,
    dgModuleConeCocone_left_triangle, Equiv.apply_symm_apply]

/-- 概要：標準 cofiber の余錐を始点に持つ境界の右データは最初の三角形で標準上側三角形に等しい。
方針：最初の余錐の右三角形の回収と標準 cofiber の余錐の三角形の計算を合成する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：右の三つの対象と g,i_C,t,v の回収。 -/
lemma dgModuleConeBoundary_right_triangle {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b =
      SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (spanBoundaryRightZeroData (sliceUnderUncurry b)).pullback (firstTriangleOrderHom (n + 1)) =
      (dgModuleConeUpperTriangle A D f).simplex.toSimplexData := by
  rw [cosliceBoundaryRightData_first_triangle b (dgModuleConeCocone A D f) hb,
    dgModuleConeCocone_right_triangle, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories

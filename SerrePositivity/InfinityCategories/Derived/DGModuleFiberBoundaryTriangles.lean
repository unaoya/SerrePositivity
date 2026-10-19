module
public import SerrePositivity.InfinityCategories.DGNerve.SliceBoundaryTriangleData
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberSquare

/-! # dg 加群の標準 fiber の錐の三角形と境界データ

概要：dg 加群の標準 fiber の錐を最後の頂点に持つ slice 境界から、その錐の二三角形を回収する。
方針：正方形と join 錐の比較、標準四角形の三角形の計算、最後の三頂点の回収を合成する。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：fiber の Hom 座標に渡す対象・射の同定。
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

/-- 概要：dg 加群の標準 fiber の錐の左三角形は指定された M を通る合成三角形。
方針：join と正方形の比較の左三角形と標準四角形の下側三角形を使う。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：左の p,g,t,u の指定。 -/
lemma dgModuleFiberCone_left_triangle (f : M ⟶ N) :
    cospanConeTriangleLeft ≫ (dgModuleFiberCone A D f).val =
      SSet.yonedaEquiv.symm (dgModuleFiberLowerTriangle A D f).simplex := by
  change cospanConeTriangleLeft ≫ (cospanConeSquareIso.hom ≫ dgModuleFiberSquare A D f) = _
  rw [← Category.assoc, cospanConeSquareIso_left, dgModuleFiberSquare_lower]

/-- 概要：dg 加群の標準 fiber の錐の右三角形は零加群を通る合成三角形。
方針：join と正方形の比較の右三角形と標準四角形の上側三角形を使う。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：右の q,h,t,v の指定。 -/
lemma dgModuleFiberCone_right_triangle (f : M ⟶ N) :
    cospanConeTriangleRight ≫ (dgModuleFiberCone A D f).val =
      SSet.yonedaEquiv.symm (dgModuleFiberUpperTriangle A D f).simplex := by
  change cospanConeTriangleRight ≫ (cospanConeSquareIso.hom ≫ dgModuleFiberSquare A D f) = _
  rw [← Category.assoc, cospanConeSquareIso_right, dgModuleFiberSquare_upper]

/-- 概要：dg 加群の標準 fiber の錐を終点に持つ境界の左データは最後の三角形で標準下側三角形に等しい。
方針：最後の錐の左三角形の回収と dg 加群の標準 fiber の錐の三角形の計算を合成する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：左の三つの対象と p,g,t,u の回収。 -/
lemma dgModuleFiberBoundary_left_triangle {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (cospanBoundaryLeftZeroData (sliceOverUncurry b)).pullback (lastTriangleOrderHom (n + 1)) =
      (dgModuleFiberLowerTriangle A D f).simplex.toSimplexData := by
  rw [sliceBoundaryLeftData_last_triangle b (dgModuleFiberCone A D f) hb,
    dgModuleFiberCone_left_triangle, Equiv.apply_symm_apply]

/-- 概要：dg 加群の標準 fiber の錐を終点に持つ境界の右データは最後の三角形で標準上側三角形に等しい。
方針：最後の錐の右三角形の回収と dg 加群の標準 fiber の錐の三角形の計算を合成する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：右の三つの対象と q,h,t,v の回収。 -/
lemma dgModuleFiberBoundary_right_triangle {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (cospanBoundaryRightZeroData (sliceOverUncurry b)).pullback (lastTriangleOrderHom (n + 1)) =
      (dgModuleFiberUpperTriangle A D f).simplex.toSimplexData := by
  rw [sliceBoundaryRightData_last_triangle b (dgModuleFiberCone A D f) hb,
    dgModuleFiberCone_right_triangle, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SliceBoundaryTriangleData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberConeVertex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexTriangleComponents

/-! # 標準 fiber の錐の三角形と境界データ

概要：標準 fiber の錐を最後の頂点に持つ slice 境界から、その錐の二三角形を回収する。
方針：正方形と join 錐の比較、標準四角形の三角形の計算、最後の三頂点の回収を合成する。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：fiber の Hom 座標に渡す対象・射の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：標準 fiber の錐の左三角形は指定された B を通る合成三角形。
方針：join と正方形の比較の左三角形と標準四角形の下側三角形を使う。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：左の p,g,t,u の指定。 -/
lemma standardFiberCone_left_triangle (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h).val =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).simplex := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_lower]

/-- 概要：標準 fiber の錐の右三角形は指定された C を通る合成三角形。
方針：join と正方形の比較の右三角形と標準四角形の上側三角形を使う。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：右の q,h,t,v の指定。 -/
lemma standardFiberCone_right_triangle (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h).val =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).simplex := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_upper]

/-- 概要：標準 fiber の錐を終点に持つ境界の左データは最後の三角形で標準下側三角形に等しい。
方針：最後の錐の左三角形の回収と標準 fiber の錐の三角形の計算を合成する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：左の三つの対象と p,g,t,u の回収。 -/
lemma fiberSliceBoundary_left_triangle {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).simplex.toSimplexData := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sliceBoundaryLeftData_last_triangle b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h) hb,
    standardFiberCone_left_triangle, Equiv.apply_symm_apply]

/-- 概要：標準 fiber の錐を終点に持つ境界の右データは最後の三角形で標準上側三角形に等しい。
方針：最後の錐の右三角形の回収と標準 fiber の錐の三角形の計算を合成する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：右の三つの対象と q,h,t,v の回収。 -/
lemma fiberSliceBoundary_right_triangle {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom (n + 1)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).simplex.toSimplexData := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sliceBoundaryRightData_last_triangle b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h) hb,
    standardFiberCone_right_triangle, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

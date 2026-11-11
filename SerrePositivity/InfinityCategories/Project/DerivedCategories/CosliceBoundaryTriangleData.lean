module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceBoundaryFromJoinFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanBoundaryFirstTriangleData

/-! # 指定された余錐の三角形のデータの回収

概要：coslice 境界の最初の頂点の余錐を、左右の境界データの最初の三角形で回収する。
方針：join 境界の最初の三角形の公式に、最初の頂点の余錐の回収を代入する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：標準 cofiber の対象・脚・高次成分の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：coslice 境界の左データの最初の三角形は指定された余錐の左三角形のデータ。
方針：最初の三角形の制限を計算し、coslice の最初の頂点の条件で余錐に置き換える。
規約：HTT §1.2.13。使われ方：標準 cofiber の f,i_B,t,u の回収。 -/
lemma cosliceBoundaryLeftData_first_triangle {n : ℕ}
    {p : (SSet.horn 2 0 : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}
    (b : (SSet.boundary (n + 1) : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm c) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ c.val)).toSimplexData := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_first_triangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cosliceBoundary_first_cocone b c hb]

/-- 概要：coslice 境界の右データの最初の三角形は指定された余錐の右三角形のデータ。
方針：最初の三角形の制限を計算し、coslice の最初の頂点の条件で余錐に置き換える。
規約：HTT §1.2.13。使われ方：標準 cofiber の g,i_C,t,v の回収。 -/
lemma cosliceBoundaryRightData_first_triangle {n : ℕ}
    {p : (SSet.horn 2 0 : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}
    (b : (SSet.boundary (n + 1) : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm c) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ c.val)).toSimplexData := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_first_triangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cosliceBoundary_first_cocone b c hb]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.JoinLastTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanBoundaryData

/-! # 境界の最後の頂点の二三角形

概要：零番目の境界面の最後の三角形は、境界の最後の頂点に付く錐の左右の三角形。
方針：標準 join の最後の三角形の公式と境界の頂点の評価を合成する。
規約：HTT §1.2.13。使われ方：標準 fiber の二つの三角形を境界の既知成分から回収する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：零番目の境界面の最後の頂点は境界全体の最後の頂点。
方針：境界の面の頂点の評価式に零番目の面と最後の頂点を代入する。
規約：HTT §1.2.12–1.2.13。使われ方：最後の錐の境界面への持ち上げ。 -/
lemma boundaryVertex_last_face_zero (n : ℕ) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫
        SSet.boundary.ι.{u} (0 : Fin (n + 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) := by
  simpa only [Fin.succAbove_zero, Fin.succ_last] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation.vertex_face.{u} (0 : Fin (n + 2)) (Fin.last n)

/-- 概要：左の零番目の境界面の最後の三角形は、最後の頂点の左錐三角形。
方針：最後の三角形の join の公式と零番目の面の最後の頂点の式を使う。
規約：HTT §1.2.13。使われ方：左の錐の脚と高次成分を回収する。 -/
lemma cospanBoundaryLeftLift_last_triangle (n : ℕ)
    (h0 : (0 : Fin (n + 4)) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom n)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftLift.{u} n 0 h0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))) (𝟙 (SSet.horn 2 2 : SSet.{u})) := by
  change SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.boundary.ι (0 : Fin (n + 2))) (𝟙 _)) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft_last_triangle, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, boundaryVertex_last_face_zero]

/-- 概要：右の零番目の境界面の最後の三角形は、最後の頂点の右錐三角形。
方針：最後の三角形の join の公式と零番目の面の最後の頂点の式を使う。
規約：HTT §1.2.13。使われ方：右の錐の脚と高次成分を回収する。 -/
lemma cospanBoundaryRightLift_last_triangle (n : ℕ)
    (h0 : (0 : Fin (n + 4)) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom n)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightLift.{u} n 0 h0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))) (𝟙 (SSet.horn 2 2 : SSet.{u})) := by
  change SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.boundary.ι (0 : Fin (n + 2))) (𝟙 _)) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight_last_triangle, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, boundaryVertex_last_face_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

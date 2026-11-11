module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.BoundaryFirstTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanBoundaryZeroData

/-! # 最初の三角形への境界データの制限

概要：左右の零未知境界データの最初の三頂点は、境界の最初の頂点の余錐の三角形を回収する。
方針：最初の三頂点を既知の最後の面で回収し、境界への持ち上げの公式を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：標準 fiber の対象・脚・ホモトピーの同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：左の零未知データの最初の三角形は、境界の最初の頂点の余錐の左三角形。
方針：最後の面の値を引き戻し、最初の三角形と境界頂点の join の公式で比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：左の標準余錐の三つの対象と全成分の回収。 -/
lemma spanBoundaryLeftZeroData_first_triangle {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0) ≫ F)).toSimplexData := by
  have h0 : Fin.last (n + 3) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces _).mpr (by change 2 ≤ n + 3; omega)
  calc
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1)) =
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).pullback
          (Fin.last (n + 3)).succAboveOrderEmb.toOrderHom).pullback
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_face_last]
    _ = (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n (Fin.last (n + 3)) h0 ≫ F)).toSimplexData.pullback
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n) := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_pullback_face F _ (Fin.last (n + 3)) h0]
    _ = (SSet.yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n (Fin.last (n + 3)) h0 ≫ F))).toSimplexData := by
      change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)).op
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n (Fin.last (n + 3)) h0 ≫ F))).toSimplexData = _
      exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData (SSet.yonedaEquiv_naturality
        (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n (Fin.last (n + 3)) h0 ≫ F))
    _ = _ := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift_first_triangle, Category.assoc]

/-- 概要：右の零未知データの最初の三角形は、境界の最初の頂点の余錐の右三角形。
方針：最後の面の値を引き戻し、最初の三角形と境界頂点の join の公式で比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：右の標準余錐の三つの対象と全成分の回収。 -/
lemma spanBoundaryRightZeroData_first_triangle {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1)) =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0) ≫ F)).toSimplexData := by
  have h0 : Fin.last (n + 3) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces _).mpr (by change 2 ≤ n + 3; omega)
  calc
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom (n + 1)) =
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).pullback
          (Fin.last (n + 3)).succAboveOrderEmb.toOrderHom).pullback
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom_face_last]
    _ = (SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n (Fin.last (n + 3)) h0 ≫ F)).toSimplexData.pullback
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n) := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_pullback_face F _ (Fin.last (n + 3)) h0]
    _ = (SSet.yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n (Fin.last (n + 3)) h0 ≫ F))).toSimplexData := by
      change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)).op
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n (Fin.last (n + 3)) h0 ≫ F))).toSimplexData = _
      exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData (SSet.yonedaEquiv_naturality
        (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n (Fin.last (n + 3)) h0 ≫ F))
    _ = _ := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift_first_triangle, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

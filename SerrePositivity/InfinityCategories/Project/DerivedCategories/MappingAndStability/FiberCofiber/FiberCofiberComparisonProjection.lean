module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberCofiberComparisonSlice
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.TriangleAppendEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-! # 双対の coslice 比較辺の射影

概要：coslice の比較辺の射影は明示的な cofiber 比較鎖写像の辺と一致する。
方針：join の右因子を左セルの最後の二頂点で計算する。
規約：端点の表記の違いを許して一単体を同定する。使われ方：D7 の比較辺の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

/-- 左セルの最後の辺は span の join の右因子。 -/
lemma spanJoinLeft_lastEdge :
    SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft.{u} 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (SSet.horn 2 0 : SSet.{u}) Δ[1] := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft
  change SSet.stdSimplex.map (SimplexCategory.mkHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberJoinRightOrderHom 1 1 3 (by omega))) ≫ _ = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberJoinStdSimplexIso_inr]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]

variable {S : Type u} [CommRing S] {B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 比較 join 写像の右因子への制限は明示的比較射の辺。 -/
lemma fiberCofiberComparisonJoin_suffix (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (SSet.horn 2 0 : SSet.{u + 1}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonJoin g h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h)).edge := by
  rw [← spanJoinLeft_lastEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_lastEdge _ _ _ _ _ _

/-- Coslice 比較辺の射影は明示的比較射と同じ一単体。 -/
lemma fiberCofiberComparisonSliceEdge_projection (g : B ⟶ D) (h : C ⟶ D) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonSliceEdge g h).map ((SSet.truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)))))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)))).app _
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonJoin g h)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonJoin_fixed g h))) = _
  rw [← SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection, fiberCofiberComparisonJoin_suffix]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories.Project.DerivedCategories

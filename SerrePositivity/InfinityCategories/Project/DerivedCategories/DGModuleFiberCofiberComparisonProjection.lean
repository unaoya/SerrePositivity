module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberCofiberComparisonSlice
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleTriangleAppendEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberCofiberComparisonProjection

/-! # 双対の coslice 比較辺の射影

概要：coslice の比較辺の射影は明示的な cofiber 比較鎖写像の辺と一致する。
方針：join の右因子を左セルの最後の二頂点で計算する。
規約：端点の表記の違いを許して一単体を同定する。使われ方：β3 の比較辺の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 比較 join 写像の右因子への制限は明示的比較射の辺。 -/
lemma dgModuleFiberCofiberComparisonJoin_suffix (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc A D f)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_lastEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_lastEdge A D _ _ _ _ _ _

/-- Coslice 比較辺の射影は明示的比較射と同じ一単体。 -/
lemma dgModuleFiberCofiberComparisonSliceEdge_projection (f : M ⟶ N) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonSliceEdge A D f).map ((SSet.truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))))).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc A D f)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))).app _
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin A D f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin_fixed A D f))) = _
  rw [← SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection,
    dgModuleFiberCofiberComparisonJoin_suffix]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCofiberFiberComparisonProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection

/-! # dg 加群の標準 cofiber 四角形の引き戻し性

概要：標準 cone 四角形は dg 加群 nerve の引き戻しでもある。
方針：実 slice 比較辺の可逆性を射影から反映し、標準 fiber の極限性を移す。
規約：安定性を前提にしない。使われ方：β3 の零角の双カルテジアン判定。
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

/-- cofiber から fiber への実際の slice 比較辺は可逆。 -/
lemma dgModuleCofiberFiberComparisonSliceEdge_isInvertible (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D (moduleConeInr A D f))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonSliceEdge A D f) := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_isInvertible A D f
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonSliceEdge_projection A D f)).mpr he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D (moduleConeInr A D f))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonSliceEdge A D f) hp

/-- 標準 dg 加群の cone 四角形は実際の ∞ 引き戻し四角形である。 -/
lemma dgModuleConeSquare_isPullback (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) := by
  have := dgModuleCofiberFiberComparisonSliceEdge_isInvertible A D f
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberSourceCone A D f) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone_isLimit A D (moduleConeInr A D f)).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonSliceEdge A D f))).symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone_isLimit (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparison_cospan A D f).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberSourceCone A D f) hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories

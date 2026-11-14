module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberCofiberComparisonProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConePushout
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.PushoutComparison

/-! # dg 加群の標準 fiber 四角形の押し出し性

概要：標準 fiber 四角形は全 Hom end の dg 加群 nerve 内で押し出しでもある。
方針：降下射の同値性を実 coslice 比較辺へ反映し、cone の余極限性を移送する。
規約：安定性を仮定しない。使われ方：β3 の零角の双カルテジアン判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 標準 cone 余錐から元の fiber 余錐への実 coslice 比較辺は可逆。 -/
lemma dgModuleFiberCofiberComparisonSliceEdge_isInvertible (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonSliceEdge A D f) := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc_isInvertible A D f
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonSliceEdge_projection A D f)).mpr he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonSliceEdge A D f) hp

/-- 標準 fiber 四角形は dg 加群 nerve の押し出しでもある。 -/
lemma dgModuleFiberSquare_isPushout (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f) := by
  have := dgModuleFiberCofiberComparisonSliceEdge_isInvertible A D f
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberTargetCocone A D f) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone_isColimit A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonSliceEdge A D f)))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rebaseCocone_isColimit_iff (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparison_span A D f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f))).mp hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories

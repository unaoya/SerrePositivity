module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGHomConeLimitCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.ConeHomTestUniverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedHomTargetComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SquareConePostcomp
/-!
概要：生の dg 入力像の実極限錐を、同じ実半自由出力分解の極限錐へ移す。
方針：元の表現可能 Hom の全関手同型を、同じ全錐の切断制限の判定へ接続する。
規約：生の出力の射影性・入力の Small 性は不要。使われ方：一般 kernel の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 同じ実錐の全 Hom 試験による分解後の極限性。 -/
lemma dgModuleResolvedInfinity_isLimitCone_of_raw
    {K : SSet.{max (u + 1) v}} {d : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone d)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F) c) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isLimitCone_iff_homTargetPointedRestriction R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) _).mpr
  intro T
  have hraw := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isLimitCone_iff_homTargetPointedRestriction R (RightModule R E) _).mp hc
    T.val
  have hraw' := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.leftFibrationConeRestriction_ulift_postcomp_iff _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T.val) c).mp hraw
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.leftFibrationConeRestriction_mapJoinCone_iff_of_functorIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedRepresentableHomSpaceIso R C E F T)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{max (u + 1) v, max (u + 1) v + 1} c)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.leftFibrationConeRestriction_ulift_postcomp_iff _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) T) c).mpr (he.mpr hraw')
/-- 同じ実錐の全 Hom 試験による分解後の極限性。 -/
lemma dgModuleResolvedInfinity_isPullbackSquare_of_raw
    (s : (Δ[1] : SSet.{max (u + 1) v}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_map_pullbackCone_iff _ s).mp
  exact dgModuleResolvedInfinity_isLimitCone_of_raw R C E F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone s)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_map_pullbackCone_iff _ s).mpr hs)
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorResolvedKernel
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence
/-!
概要：元の小 Perf Milnor 対角と同じ cell 平坦商の Verdier 列を構成する。
方針：対角の充満忠実性、厚い核の本質像、辺局所化を接続する。
規約：生成判定と前三角性の上流接続は明示入力であり、未分解 path 商は使わない。
使われ方：K-S• が元商射影を cell 平坦商へ付け替えるための供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
  [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d)]
  [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal)]
theorem dgGluingMilnor_isResolvedVerdierSequence
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hgen : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSmallPerfectGeneration R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d) where
  fullyFaithful := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSmallPerfectDiagonal_isFullyFaithful R d h hgen
  kernel := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedQuotient_zero_iff R d h hgen
  quotient := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedQuotient_isLocalization R d h hgen
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryGlobalPullbackComponents
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.PullbackCommonNormalizedIso

/-!
概要：coherent な二次元境界比較と元の大域作用を、同じ pullback 上の関手同型で結ぶ。
方針：面・ホーン成分の共有境界像の一致と実際の pullback の射影等式を使う。
規約：元の全 Hom と元の分類主写像を保持する。
使われ方：実際の標準境界比較を元の大域作用へ戻す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable (j : Fin 2) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "q₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceTargetRestriction p q
local notation "q₂" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornTargetRestriction p q
local notation "a" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCorrectedGlobalPullbackMap j p q
local notation "b" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryOriginalGlobalPullbackMap p q
local instance : HasPullback q₁ q₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan q₁ q₂)

/-- 同じ二射の面・ホーンの指定同型は共有境界で整合し、pullback 上で貼り合う。 -/
def cocartesianTwoBoundaryGlobalPullbackComparisonIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b := by
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryGlobalPullbackFaceComponentIso j p q
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryGlobalPullbackHornComponentIso j p q
  have h : HEq (L.postcomp q₁) (R.postcomp q₂) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryGlobalPullbackFaceComponentIso_shared_heq j p q).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryGlobalPullbackHornComponentIso_shared_heq j p q).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackFunctorIsoOfCommonNormalizedIsos q₁ q₂ a b L R rfl rfl
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq q₁ q₂ a).symm
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq q₁ q₂ b).symm
    (eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans
      (h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm)))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

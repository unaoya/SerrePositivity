module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryGlobalPullbackTarget
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryDiagramOriginal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryCoherentHornOriginal
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointProjection

/-!
概要：同じ境界 pullback への二射を、面・ホーンの元の指定同型で成分ごとに結ぶ。
方針：両射影の等式だけで同型の端点を揃える。
規約：元の分類主写像と共有境界での指定像を保持する。
使われ方：coherent な境界比較の大域同型を貼り合わせる。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable (j : Fin 2) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ
local notation "q₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceTargetRestriction p q
local notation "q₂" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornTargetRestriction p q
local instance : HasPullback q₁ q₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan q₁ q₂)

/-- 面側の実際の射影を、同じ元の補正面の大域同型で結ぶ。 -/
def cocartesianTwoBoundaryGlobalPullbackFaceComponentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCorrectedGlobalPullbackMap j p q ≫ pullback.fst q₁ q₂)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryOriginalGlobalPullbackMap p q ≫ pullback.fst q₁ q₂) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryDiagramOriginalIso j τ p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCorrectedGlobalPullbackMap_fst j p q).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryOriginalGlobalPullbackMap_fst p q).symm

/-- 面側の実際の射影成分も、同じ共有境界での指定像を保つ。 -/
lemma cocartesianTwoBoundaryGlobalPullbackFaceComponentIso_shared_heq :
    HEq ((cocartesianTwoBoundaryGlobalPullbackFaceComponentIso j p q).postcomp q₁)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryDiagramOriginalIso j τ p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCorrectedGlobalPullbackMap_fst j p q).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryOriginalGlobalPullbackMap_fst p q).symm q₁).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryDiagramOriginalIso_shared_heq j τ p q)

/-- ホーン側の実際の射影を、coherent な補正ホーンの大域同型で結ぶ。 -/
def cocartesianTwoBoundaryGlobalPullbackHornComponentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCorrectedGlobalPullbackMap j p q ≫ pullback.snd q₁ q₂)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryOriginalGlobalPullbackMap p q ≫ pullback.snd q₁ q₂) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCoherentHornComparison_originalIso j p q)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCorrectedGlobalPullbackMap_snd j p q).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryOriginalGlobalPullbackMap_snd p q).symm

/-- ホーン側の実際の射影成分も、面側が指定した同じ共有境界像を保つ。 -/
lemma cocartesianTwoBoundaryGlobalPullbackHornComponentIso_shared_heq :
    HEq ((cocartesianTwoBoundaryGlobalPullbackHornComponentIso j p q).postcomp q₂)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCoherentHornComparison_originalIso j p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCorrectedGlobalPullbackMap_snd j p q).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryOriginalGlobalPullbackMap_snd p q).symm q₂).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCoherentHornComparison_originalIso_shared_heq j p q)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

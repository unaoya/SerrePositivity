module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HornBoundaryDiagramPullbacks
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryPullbackComparison

/-!
概要：実際の二次元境界の native Hom を、構成済みの同じ cospan の pullback と同一視する。
方針：元の境界の降下を、標準境界の同じ端点表示へ揃える。
規約：元の面・ホーンへの両射影を保持する。
使われ方：厳密 pullback 比較を実際の境界 Hom へ戻す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryNativePresentation
variable (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftCoreFunctor p.val.hom q.val.hom
local notation "p₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceNativeRestriction p q
local notation "p₂" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornNativeRestriction p q

local instance : HasPullback p₁ p₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan p₁ p₂)

/-- 同じ反変図式の実際の二次元境界は、同じ二つの制限の pullback。 -/
lemma cocartesianTwoBoundaryNative_isPullback :
    IsPullback ((N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.faceInclusion 1 1 σ).op)
      ((N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion 1 1 σ).op) p₁ p₂ := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHornBoundary_nativeDiagram_isPullback 1 1 σ p.val.hom q.val.hom
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftCoreFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceNativeRestriction,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornNativeRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalSourceRestriction,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundarySharedToHorn, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.toFace,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.shared, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.face,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.horn, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver] using h

/-- 実際の境界の同じ native Hom を、同じ二つの制限の厳密 pullback へ移す。 -/
def cocartesianTwoBoundaryNativePresentationIso :
    (N).obj (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 1 σ)) ≅ pullback p₁ p₂ :=
  (cocartesianTwoBoundaryNative_isPullback p q).isoPullback

/-- 同じ表示同型は元の面への制限を保持する。 -/
lemma cocartesianTwoBoundaryNativePresentationIso_hom_fst :
    (cocartesianTwoBoundaryNativePresentationIso p q).hom ≫ pullback.fst p₁ p₂ =
      (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.faceInclusion 1 1 σ).op :=
  (cocartesianTwoBoundaryNative_isPullback p q).isoPullback_hom_fst

/-- 同じ表示同型は元のホーンへの制限も保持する。 -/
lemma cocartesianTwoBoundaryNativePresentationIso_hom_snd :
    (cocartesianTwoBoundaryNativePresentationIso p q).hom ≫ pullback.snd p₁ p₂ =
      (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion 1 1 σ).op :=
  (cocartesianTwoBoundaryNative_isPullback p q).isoPullback_hom_snd

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryNativePresentation

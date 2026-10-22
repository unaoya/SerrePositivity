module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundaryGlobalPullbackTarget
public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryDiagramOriginal
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundaryCoherentHornOriginal
public import SerrePositivity.InfinityCategories.F1.FunctorIsoEndpointProjection

/-!
概要：同じ境界 pullback への二射を、面・ホーンの元の指定同型で成分ごとに結ぶ。
方針：両射影の等式だけで同型の端点を揃える。
規約：元の分類主写像と共有境界での指定像を保持する。
使われ方：coherent な境界比較の大域同型を貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ
local notation "q₁" => cocartesianTwoBoundaryFaceTargetRestriction p q
local notation "q₂" => cocartesianTwoBoundaryHornTargetRestriction p q
local instance : HasPullback q₁ q₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan q₁ q₂)

/-- 面側の実際の射影を、同じ元の補正面の大域同型で結ぶ。 -/
def cocartesianTwoBoundaryGlobalPullbackFaceComponentIso :
    FunctorIso (cocartesianTwoBoundaryCorrectedGlobalPullbackMap j p q ≫ pullback.fst q₁ q₂)
      (cocartesianTwoBoundaryOriginalGlobalPullbackMap p q ≫ pullback.fst q₁ q₂) :=
  F2.functorIsoOfEq (cocartesianOneBoundaryDiagramOriginalIso j τ p q)
    (cocartesianTwoBoundaryCorrectedGlobalPullbackMap_fst j p q).symm
    (cocartesianTwoBoundaryOriginalGlobalPullbackMap_fst p q).symm

/-- 面側の実際の射影成分も、同じ共有境界での指定像を保つ。 -/
lemma cocartesianTwoBoundaryGlobalPullbackFaceComponentIso_shared_heq :
    HEq ((cocartesianTwoBoundaryGlobalPullbackFaceComponentIso j p q).postcomp q₁)
      (cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) := by
  exact (functorIsoOfEq_postcomp_heq (cocartesianOneBoundaryDiagramOriginalIso j τ p q)
    (cocartesianTwoBoundaryCorrectedGlobalPullbackMap_fst j p q).symm
    (cocartesianTwoBoundaryOriginalGlobalPullbackMap_fst p q).symm q₁).trans
    (cocartesianOneBoundaryDiagramOriginalIso_shared_heq j τ p q)

/-- ホーン側の実際の射影を、coherent な補正ホーンの大域同型で結ぶ。 -/
def cocartesianTwoBoundaryGlobalPullbackHornComponentIso :
    FunctorIso (cocartesianTwoBoundaryCorrectedGlobalPullbackMap j p q ≫ pullback.snd q₁ q₂)
      (cocartesianTwoBoundaryOriginalGlobalPullbackMap p q ≫ pullback.snd q₁ q₂) := by
  apply F2.functorIsoOfEq (cocartesianTwoBoundaryCoherentHornComparison_originalIso j p q)
  · exact (cocartesianTwoBoundaryCorrectedGlobalPullbackMap_snd j p q).symm
  · exact (cocartesianTwoBoundaryOriginalGlobalPullbackMap_snd p q).symm

/-- ホーン側の実際の射影成分も、面側が指定した同じ共有境界像を保つ。 -/
lemma cocartesianTwoBoundaryGlobalPullbackHornComponentIso_shared_heq :
    HEq ((cocartesianTwoBoundaryGlobalPullbackHornComponentIso j p q).postcomp q₂)
      (cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) := by
  exact (functorIsoOfEq_postcomp_heq
    (cocartesianTwoBoundaryCoherentHornComparison_originalIso j p q)
    (cocartesianTwoBoundaryCorrectedGlobalPullbackMap_snd j p q).symm
    (cocartesianTwoBoundaryOriginalGlobalPullbackMap_snd p q).symm q₂).trans
    (cocartesianTwoBoundaryCoherentHornComparison_originalIso_shared_heq j p q)

end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoBoundaryNativePresentation

/-!
概要：実際の二次元境界の分類先 Hom を、同じ cospan の厳密 pullback と同一視する。
方針：元の境界の降下を、同じ標準境界の端点表示へ揃える。
規約：元の面・ホーンへの両射影を保持する。
使われ方：同じ pullback 比較を実際の分類先の境界 Hom へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "T" => intervalDiagramLiftOverFunctor P Q
local notation "q₁" => cocartesianTwoBoundaryFaceTargetRestriction p q
local notation "q₂" => cocartesianTwoBoundaryHornTargetRestriction p q

local instance : HasPullback q₁ q₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan q₁ q₂)

/-- 同じ分類先の実際の二次元境界 Hom は、同じ二つの制限の pullback。 -/
lemma cocartesianTwoBoundaryTarget_isPullback :
    IsPullback ((T).map (HornBoundaryOver.faceInclusion 1 1 σ).op)
      ((T).map (HornBoundaryOver.hornInclusion 1 1 σ).op) q₁ q₂ := by
  have h := cocartesianHornBoundary_targetDiagram_isPullback 1 1 σ P Q
  simpa only [intervalDiagramLiftOverFunctor, cocartesianTwoBoundaryFaceTargetRestriction,
    cocartesianTwoBoundaryHornTargetRestriction, cocartesianOneBoundaryLocalTargetRestriction,
    cocartesianTwoBoundarySharedToHorn, boundarySimplexOverMap, HornBoundaryOver.toFace,
    HornBoundaryOver.shared, HornBoundaryOver.apex, HornBoundaryOver.face,
    HornBoundaryOver.horn, cocartesianFiniteHornOver] using h

/-- 実際の分類先境界 Hom を、同じ二制限の厳密 pullback へ移す。 -/
def cocartesianTwoBoundaryTargetPresentationIso :
    (T).obj (Opposite.op (HornBoundaryOver.apex 1 σ)) ≅ pullback q₁ q₂ :=
  (cocartesianTwoBoundaryTarget_isPullback p q).isoPullback

/-- 同じ表示同型は元の面への制限を保持する。 -/
lemma cocartesianTwoBoundaryTargetPresentationIso_hom_fst :
    (cocartesianTwoBoundaryTargetPresentationIso p q).hom ≫ pullback.fst q₁ q₂ =
      (T).map (HornBoundaryOver.faceInclusion 1 1 σ).op :=
  (cocartesianTwoBoundaryTarget_isPullback p q).isoPullback_hom_fst

/-- 同じ表示同型は元のホーンへの制限も保持する。 -/
lemma cocartesianTwoBoundaryTargetPresentationIso_hom_snd :
    (cocartesianTwoBoundaryTargetPresentationIso p q).hom ≫ pullback.snd q₁ q₂ =
      (T).map (HornBoundaryOver.hornInclusion 1 1 σ).op :=
  (cocartesianTwoBoundaryTarget_isPullback p q).isoPullback_hom_snd

end SerrePositivity.InfinityCategories

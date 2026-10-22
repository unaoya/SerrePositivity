module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundaryGlobalPullbackComponents
public import SerrePositivity.InfinityCategories.F1.PullbackCommonNormalizedIso

/-!
概要：coherent な二次元境界比較と元の大域作用を、同じ pullback 上の関手同型で結ぶ。
方針：面・ホーン成分の共有境界像の一致と実際の pullback の射影等式を使う。
規約：元の全 Hom と元の分類主写像を保持する。
使われ方：実際の標準境界比較を元の大域作用へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "q₁" => cocartesianTwoBoundaryFaceTargetRestriction p q
local notation "q₂" => cocartesianTwoBoundaryHornTargetRestriction p q
local notation "a" => cocartesianTwoBoundaryCorrectedGlobalPullbackMap j p q
local notation "b" => cocartesianTwoBoundaryOriginalGlobalPullbackMap p q
local instance : HasPullback q₁ q₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan q₁ q₂)

/-- 同じ二射の面・ホーンの指定同型は共有境界で整合し、pullback 上で貼り合う。 -/
def cocartesianTwoBoundaryGlobalPullbackComparisonIso : FunctorIso a b := by
  let L := cocartesianTwoBoundaryGlobalPullbackFaceComponentIso j p q
  let R := cocartesianTwoBoundaryGlobalPullbackHornComponentIso j p q
  have h : HEq (L.postcomp q₁) (R.postcomp q₂) :=
    (cocartesianTwoBoundaryGlobalPullbackFaceComponentIso_shared_heq j p q).trans
      (cocartesianTwoBoundaryGlobalPullbackHornComponentIso_shared_heq j p q).symm
  exact pullbackFunctorIsoOfCommonNormalizedIsos q₁ q₂ a b L R rfl rfl
    (pullbackProjectionComposite_eq q₁ q₂ a).symm
    (pullbackProjectionComposite_eq q₁ q₂ b).symm
    (eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
      (h.trans (F2.functorIsoOfEq_heq _ _ _).symm)))

end SerrePositivity.InfinityCategories

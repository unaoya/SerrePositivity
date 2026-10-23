module

public import SerrePositivity.InfinityCategories.F1.ScaffoldBridgeHomPullbacks
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldBridgeCoreRestriction

/-!
概要：元の全 Hom の core から最初の区間と尾部の厳密 pullback への Segal 射は自明 Kan。
方針：同じ元の制限と、同じ二成分の厳密な pullback 同型を合成する。
規約：両射影は元の全 Hom からの直接制限そのもの。
使われ方：高次単体で元の分類 Hom 作用の同値性を反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {E F : SSet.{u}}
  (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [CocartesianFibration p]
  (q : F ⟶ nerve (ULift.{u} (Fin (n + 2)))) [CocartesianFibration q]
local notation "H" => scaffoldFiniteNerveBridge n

/-- 元の全 Hom の core から同じ二成分の厳密な pullback への射。 -/
def cocartesianScaffoldBridgeSourceSegalMap :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (quasicategoryCore (cocartesianRelativeFunctorSpace p q) : SSet.{u}) ⟶
    pullback (cocartesianPullbackNativeLiftPre p q (ScaffoldBridgeOver.toFirst n H))
      (cocartesianPullbackNativeLiftPre p q (ScaffoldBridgeOver.toTail n H)) :=
  cocartesianPullbackNativeLiftRestriction p q (Over.mk H) ≫
    (ScaffoldBridgeOver.nativeLift_isPullback n H p q).isoPullback.hom

/-- 同じ Segal 射の最初の射影は、元の最初の区間への直接制限。 -/
lemma cocartesianScaffoldBridgeSourceSegalMap_fst :
    cocartesianScaffoldBridgeSourceSegalMap n p q ≫ pullback.fst _ _ =
      cocartesianPullbackNativeLiftRestriction p q (ScaffoldBridgeOver.first n H) := by
  rw [cocartesianScaffoldBridgeSourceSegalMap, Category.assoc, IsPullback.isoPullback_hom_fst]
  exact cocartesianPullbackNativeLiftRestriction_naturality p q
    (ScaffoldBridgeOver.firstInclusion n H)

/-- 同じ Segal 射の尾部の射影も、元の尾部単体への直接制限。 -/
lemma cocartesianScaffoldBridgeSourceSegalMap_snd :
    cocartesianScaffoldBridgeSourceSegalMap n p q ≫ pullback.snd _ _ =
      cocartesianPullbackNativeLiftRestriction p q (ScaffoldBridgeOver.tail n H) := by
  rw [cocartesianScaffoldBridgeSourceSegalMap, Category.assoc, IsPullback.isoPullback_hom_snd]
  exact cocartesianPullbackNativeLiftRestriction_naturality p q
    (ScaffoldBridgeOver.tailInclusion n H)

/-- この同じ全 Hom 上の二成分 Segal 射は、全次元で自明 Kan。 -/
lemma cocartesianScaffoldBridgeSourceSegalMap_trivialKanFibration :
    TrivialKanFibration (cocartesianScaffoldBridgeSourceSegalMap n p q) :=
  ⟨trivialKanFibrations.comp_mem _ _
    (cocartesianPullbackNativeLiftRestriction_scaffoldBridge_trivialKanFibration n p q).mem
    (trivialKanFibrations.of_isIso _)⟩

end SerrePositivity.InfinityCategories

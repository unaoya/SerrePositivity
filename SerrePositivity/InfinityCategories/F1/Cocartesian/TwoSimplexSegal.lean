module

public import SerrePositivity.InfinityCategories.F1.InnerTwoHornHomPullbacks
public import SerrePositivity.InfinityCategories.F1.Cocartesian.InnerTwoHornRestriction

/-!
概要：二次元単体上の元の Hom の core を、二区間の元の Hom の pullback と比較する。
方針：同じ内ホーンへの自明 Kan 制限と、同じ二射影の厳密な pullback 表示を合成する。
規約：元の Hom の同じ制限写像を使う。
使われ方：元の分類 Hom 作用の二次元 Segal 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open InnerTwoHornOver

variable {E F : SSet.{u}} (p : E ⟶ (Δ[2] : SSet.{u})) [CocartesianFibration p]
  (q : F ⟶ (Δ[2] : SSet.{u})) [CocartesianFibration q]

/-- 元の二次元 Hom の core から、同じ二区間の Hom の厳密な pullback への比較。 -/
def cocartesianTwoSimplexSegalMap :
    (quasicategoryCore (cocartesianRelativeFunctorSpace p q) : SSet.{u}) ⟶
      pullback
        (quasicategoryCoreMap (cocartesianPullbackNativePre p q (toSecond (horn 2 1).ι)))
        (quasicategoryCoreMap (cocartesianPullbackNativePre p q (toFirst (horn 2 1).ι))) :=
  quasicategoryCoreMap (cocartesianPullbackNativeRestriction p q (Over.mk (horn 2 1).ι)) ≫
    (nativeCore_isPullback p q (horn 2 1).ι).isoPullback.hom

/-- 元の二区間への同じ比較は、全パラメーターで自明 Kan fibration。 -/
lemma cocartesianTwoSimplexSegalMap_trivialKanFibration :
    TrivialKanFibration (cocartesianTwoSimplexSegalMap p q) := by
  exact ⟨trivialKanFibrations.comp_mem _ _
    (core_cocartesianPullbackNativeRestriction_innerTwoHorn_trivialKanFibration p q).mem
    (trivialKanFibrations.of_isIso _)⟩

/-- 最初の射影は、同じホーンから次の区間への元の制限。 -/
lemma cocartesianTwoSimplexSegalMap_fst :
    cocartesianTwoSimplexSegalMap p q ≫ pullback.fst _ _ =
      quasicategoryCoreMap
        (cocartesianPullbackNativeRestriction p q (Over.mk (horn 2 1).ι)) ≫
      quasicategoryCoreMap
        (cocartesianPullbackNativePre p q (secondInclusion (horn 2 1).ι)) := by
  rw [cocartesianTwoSimplexSegalMap, Category.assoc, IsPullback.isoPullback_hom_fst]

/-- 二番目の射影は、同じホーンから最初の区間への元の制限。 -/
lemma cocartesianTwoSimplexSegalMap_snd :
    cocartesianTwoSimplexSegalMap p q ≫ pullback.snd _ _ =
      quasicategoryCoreMap
        (cocartesianPullbackNativeRestriction p q (Over.mk (horn 2 1).ι)) ≫
      quasicategoryCoreMap
        (cocartesianPullbackNativePre p q (firstInclusion (horn 2 1).ι)) := by
  rw [cocartesianTwoSimplexSegalMap, Category.assoc, IsPullback.isoPullback_hom_snd]

end SerrePositivity.InfinityCategories

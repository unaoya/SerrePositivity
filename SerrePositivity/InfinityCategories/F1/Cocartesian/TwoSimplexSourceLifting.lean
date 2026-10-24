module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexStrictComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackCoreFibration
public import SerrePositivity.InfinityCategories.F1.KanModels.KanFibrationEquivalenceLifting

/-!
概要：同じ共有頂点への源 cospan の最初の制限は、元の全局所 Hom 上で Kan fibration。
方針：元の単射な底上の制限の core の充填性を、同じ宇宙持ち上げへ移す。
規約：追加の持ち上げ仮定を置かない。
使われ方：厳密な局所 cospan 比較の pullback 上の同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の源 cospan の最初の脚は、同じ共有頂点への全局所 Hom の Kan fibration。 -/
lemma cocartesianTwoSimplexLocalSource_first_fibration :
    Fibration ((cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inl) := by
  have : Fibration (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
      (cocartesianTwoSimplexSharedToFirst k))) :=
    core_cocartesianPullbackNativePre_fibration p.val.hom q.val.hom _
  change Fibration ((SSet.uliftFunctor.{u + 1, u}).map
    (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
      (cocartesianTwoSimplexSharedToFirst k))))
  exact fibration_uliftFunctor_map _

/-- 同じ源 cospan の最初の脚は、元の Kan 複体間で同値を持ち上げる。 -/
lemma cocartesianTwoSimplexLocalSource_first_kanEquivalenceLifting :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting
      ((cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inl) := by
  have := cocartesianTwoSimplexLocalSource_first_fibration k p q
  intro T U j hj he
  exact kanEquivalenceLifting_of_kanFibration
    ((cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inl) j hj he

end SerrePositivity.InfinityCategories

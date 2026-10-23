module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldBridgeRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeLiftRestriction
public import SerrePositivity.InfinityCategories.F1.Universe.TrivialKanFibration

/-!
概要：最初の辺と尾部への元の Hom の core の制限は、全次元・宇宙持ち上げ後も自明 Kan。
方針：元の Hom の制限を core、native Hom 同型、宇宙持ち上げへ順に移す。
規約：元の全相対 Hom の同じ制限を保持する。
使われ方：高次単体での source Segal 制限の同値性。
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

/-- 全次元で同じ元の指定辺保存 Hom の core の制限は自明 Kan。 -/
lemma core_cocartesianPullbackHomRestriction_scaffoldBridge_trivialKanFibration :
    TrivialKanFibration (quasicategoryCoreMap
      (cocartesianPullbackHomRestriction p q (Over.mk (scaffoldFiniteNerveBridge n)))) := by
  letI := cocartesianPullbackHomRestriction_scaffoldBridge_trivialKanFibration n p q
  letI : Quasicategory (cocartesianPullbackHomSpace p q
      (Over.mk (scaffoldFiniteNerveBridge n))) := by
    unfold cocartesianPullbackHomSpace
    infer_instance
  exact F2.coreMap_trivialKanFibration _

/-- 同じ底変換の native Hom の core の制限も、全次元で自明 Kan。 -/
lemma core_cocartesianPullbackNativeRestriction_scaffoldBridge_trivialKanFibration :
    TrivialKanFibration (quasicategoryCoreMap
      (cocartesianPullbackNativeRestriction p q (Over.mk (scaffoldFiniteNerveBridge n)))) := by
  let a : Over (nerve (ULift.{u} (Fin (n + 2)))) := Over.mk (scaffoldFiniteNerveBridge n)
  change TrivialKanFibration (quasicategoryCoreFunctor.map
    (cocartesianPullbackHomRestriction p q a ≫ (cocartesianPullbackHomIso p q a).inv))
  rw [CategoryTheory.Functor.map_comp]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (core_cocartesianPullbackHomRestriction_scaffoldBridge_trivialKanFibration n p q).mem
    (trivialKanFibrations.of_isIso _)⟩

/-- 分類先と同じ宇宙へ移した元の native core 制限も自明 Kan。 -/
lemma cocartesianPullbackNativeLiftRestriction_scaffoldBridge_trivialKanFibration :
    TrivialKanFibration
      (cocartesianPullbackNativeLiftRestriction p q (Over.mk (scaffoldFiniteNerveBridge n))) := by
  letI := core_cocartesianPullbackNativeRestriction_scaffoldBridge_trivialKanFibration n p q
  exact trivialKanFibration_uliftFunctor_map _

end SerrePositivity.InfinityCategories

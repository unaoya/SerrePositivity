module
public import SerrePositivity.KST.Fibration.CompletedTwoMultiEquivalence
public import SerrePositivity.KST.Fibration.RelativePullbackMulti
public import SerrePositivity.KST.Fibration.ComposableWeakSingleStep
public import SerrePositivity.KST.Fibration.CompletedTwoJointReflection

/-! # 元の二辺の第一辺・第二 cofiber 比較の全正有限反復 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 補完した二辺模型の元の引き戻しと実普遍性の共同反映を保持する。 -/
def completedTwoRelativePullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    RelativePullback (sInputModel B) (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q) where
  total := completedTwoModel q
  base := weakArrowModel q
  cofiber := completedTwoCofiber q
  projection := completedTwoFirst q
  endpoint := weakArrowTargetTopExact q
  isPullback := completedTwo_isPullback q
  reflects := completedTwo_jointReflection q

/-- 元の同じ切断を通すと、任意の関手の下で第一辺と既存の第二 cofiber を回収する。 -/
lemma completedTwoSection_pair {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (F : StableModel.{u} ⥤ SSet.{u}) :
    F.map (completedTwoSection q) ≫ (completedTwoRelativePullback q).pair F =
      lift (F.map (composableWeakFirstExact q)) (F.map (composableWeakCofiberExact q 1)) := by
  unfold RelativePullback.pair
  rw [comp_lift, ← F.map_comp, ← F.map_comp]
  apply congrArg₂ lift
  · change F.map
      (completedTwoSection q ≫ (completedTwoForget q ≫ composableWeakFirstExact q)) = _
    rw [← Category.assoc, completedTwoSection_forget, Category.id_comp]
  · change F.map (completedTwoSection q ≫ (completedTwoCofiber q ≫
      relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q))) = _
    rw [← Category.assoc, completedTwoSection_cofiber]
    rfl

/-- 元の接続した二辺から第一辺と同じ第二 cofiber への射対は全正有限反復で局所化同型。 -/
theorem composableWeakMultiStep_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (composableWeakMultiStep q (r + 1))) := by
  have := completedTwoSection_multi_localized_isIso q r
  have := (completedTwoRelativePullback q).multiPair_localized_isIso r
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (lift ((multiRealizationFunctor (r + 1)).map (composableWeakFirstExact q))
      ((multiRealizationFunctor (r + 1)).map (composableWeakCofiberExact q 1))))
  rw [← completedTwoSection_pair, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration

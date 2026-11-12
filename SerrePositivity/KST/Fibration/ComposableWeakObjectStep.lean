module
public import SerrePositivity.KST.Fibration.CompletedTwoSection
public import SerrePositivity.KST.Fibration.RelativeCofiberBaseChange
public import SerrePositivity.KST.Fibration.WeakStringTwoCutComparison

/-! # 二つの W 辺の元の object S から第一辺と第二 cofiber への比較同値 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 補完した模型の元の第一辺と、保持した第二辺の核値 cofiber の射対。 -/
def completedTwoModelObjectComparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    objectSConstructionFunctor.obj (completedTwoModel q) ⟶
      objectSConstructionFunctor.obj (weakArrowModel q) ⊗
        objectSConstructionFunctor.obj (closedStableModel (kernelClosedPredicate q)) :=
  lift (objectSConstructionFunctor.map (completedTwoFirst q))
    (objectSConstructionFunctor.map (completedTwoCofiber q) ≫
      objectSConstructionFunctor.map (relativeCofiberQuotient
        (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)))

/-- 補完した安定模型の同じ二成分は K-1/K-2 により局所化同型。 -/
lemma completedTwoModelObjectComparison_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (completedTwoModelObjectComparison q)) :=
  relativeCofiberBaseChange_localized_isIso (ClosedStablePredicate.top (sInputModel B))
    (kernelClosedPredicate q) (completedTwo_objectS_isPullback q)

/-- 元の接続した二辺から、元の第一辺と同じ第二辺の cofiber を抽出する object S の射対。 -/
def composableWeakObjectStep {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    objectSConstructionFunctor.obj (composableWeakArrowModel q) ⟶
      objectSConstructionFunctor.obj (weakArrowModel q) ⊗
        objectSConstructionFunctor.obj (closedStableModel (kernelClosedPredicate q)) :=
  lift (objectSConstructionFunctor.map (composableWeakFirstExact q))
    (objectSConstructionFunctor.map (composableWeakCofiberExact q 1))

/-- 切断を通る比較は、元の二辺と既存の第二 cofiber 選択を厳密に回収する。 -/
lemma completedTwoSection_objectStep {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    objectSConstructionFunctor.map (completedTwoSection q) ≫
      completedTwoModelObjectComparison q = composableWeakObjectStep q := by
  unfold completedTwoModelObjectComparison composableWeakObjectStep
  rw [comp_lift]
  apply congrArg₂ lift
  · rw [← CategoryTheory.Functor.map_comp]
    change objectSConstructionFunctor.map
      (completedTwoSection q ≫ (completedTwoForget q ≫ composableWeakFirstExact q)) = _
    rw [← Category.assoc, completedTwoSection_forget, Category.id_comp]
  · rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, completedTwoSection_cofiber,
      ← CategoryTheory.Functor.map_comp]
    rfl

/-- 元の接続した二辺の object S の射対は、追加仮定なしで局所化同型。 -/
theorem composableWeakObjectStep_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (composableWeakObjectStep q)) := by
  have := completedTwoSection_objectS_localized_isIso q
  have := completedTwoModelObjectComparison_localized_isIso q
  rw [← completedTwoSection_objectStep, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration

module
public import SerrePositivity.KST.Fibration.ComposableWeakObjectStep
public import SerrePositivity.KST.Fibration.ObjectSinglePairComparison

/-! # 接続した二つの W 辺の単回実現から第一辺と第二 cofiber への比較同値 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 同じ第一 W 辺と同じ第二 cofiber の全有限反復の元の射対。 -/
def composableWeakMultiStep {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    (multiRealizationFunctor r).obj (composableWeakArrowModel q) ⟶
      (multiRealizationFunctor r).obj (weakArrowModel q) ⊗
        (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)) :=
  lift ((multiRealizationFunctor r).map (composableWeakFirstExact q))
    ((multiRealizationFunctor r).map (composableWeakCofiberExact q 1))

/-- 元の二辺の単回実現の射対は局所化同型。 -/
theorem composableWeakMultiStep_one_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (composableWeakMultiStep q 1)) :=
  singlePair_localized_isIso_of_objectPair (composableWeakFirstExact q)
    (composableWeakCofiberExact q 1) (composableWeakObjectStep_localized_isIso q)

end SerrePositivity.KST.Fibration

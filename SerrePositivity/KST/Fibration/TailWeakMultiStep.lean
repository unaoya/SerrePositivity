module
public import SerrePositivity.KST.Fibration.TailRelativeCompletion
public import SerrePositivity.KST.Fibration.WeakStringTailEquivalence

/-! # 元の先行 W 列と最後の核値 cofiber への全正有限反復での比較同値 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 貼り合わせから元の最後の辺の核値 cofiber を取る完全関手。 -/
def tailWeakCofiberExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    tailWeakModel q n ⟶ closedStableModel (kernelClosedPredicate q) :=
  tailWeakEdgeExact q n ≫ (weakArrowCofiberEquivalence q).inv ≫
    relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)

/-- 元の先行列と最後の核値 cofiber の、順序を固定した反復実現の射対。 -/
def tailWeakMultiStep {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    (multiRealizationFunctor r).obj (tailWeakModel q n) ⟶
      (multiRealizationFunctor r).obj (weakStringModel q ⦋n + 1⦌) ⊗
        (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)) :=
  lift ((multiRealizationFunctor r).map (tailWeakPrefixExact q n))
    ((multiRealizationFunctor r).map (tailWeakCofiberExact q n))

/-- 同じ補完切断を通る比較は、元の先行列と既存の最後の cofiber 選択を厳密に回収する。 -/
lemma tailCompletionSection_pair {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)
    (F : StableModel.{u} ⥤ SSet.{u}) :
    F.map (weakCofiberCompletionSection q (tailWeakEdgeExact q n)) ≫
      (tailRelativePullback q n).pair F =
        lift (F.map (tailWeakPrefixExact q n)) (F.map (tailWeakCofiberExact q n)) := by
  unfold RelativePullback.pair
  rw [comp_lift, ← F.map_comp, ← F.map_comp]
  apply congrArg₂ lift
  · change F.map (weakCofiberCompletionSection q (tailWeakEdgeExact q n) ≫
      (weakCofiberCompletionForget q (tailWeakEdgeExact q n) ≫ tailWeakPrefixExact q n)) = _
    rw [← Category.assoc, weakCofiberCompletionSection_forget, Category.id_comp]
  · change F.map (weakCofiberCompletionSection q (tailWeakEdgeExact q n) ≫
      (weakCofiberCompletionCofiber q (tailWeakEdgeExact q n) ≫
        relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B))
          (kernelClosedPredicate q))) = _
    rw [← Category.assoc, weakCofiberCompletionSection_cofiber]
    rfl

/-- 元の先行列と最後の核値 cofiber の射対は、全正有限反復で局所化同型。 -/
theorem tailWeakMultiStep_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (tailWeakMultiStep q n (r + 1))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map
      (weakCofiberCompletionSection q (tailWeakEdgeExact q n)))) :=
    multiRealization_map_localized_isIso_of_equivalence r
      (weakCofiberCompletionEquivalence q (tailWeakEdgeExact q n)).symm
  have := (tailRelativePullback q n).multiPair_localized_isIso r
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (lift ((multiRealizationFunctor (r + 1)).map (tailWeakPrefixExact q n))
      ((multiRealizationFunctor (r + 1)).map (tailWeakCofiberExact q n))))
  rw [← tailCompletionSection_pair, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration

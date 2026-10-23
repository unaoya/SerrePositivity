module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwiseRestrictionPullback
public import SerrePositivity.InfinityCategories.F1.LeftAnodynePushoutProduct

/-!
概要：底を固定した形状制限の相対持ち上げ性。
方針：既存の相対内部 Hom の持ち上げ性を厳密な引き戻しで輸送する。
規約：底の quasicategory 性は不要。
使われ方：底を固定した path の両端評価と始点評価の相対充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：単射な形状制限は定値底の全空間間の left fibration。
方針：相対内部 Hom の left fibration 性を底変換し、元の制限射に同型で戻す。
規約：元の底を保持。使われ方：path の両端を同時に固定する持ち上げ。 -/
instance fiberwiseFunctorRestriction_leftFibration {A K E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (i : A ⟶ K) [Mono i] :
    LeftFibration (fiberwiseFunctorRestriction p i) := by
  let r := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := leftFibration_pullbackObjObjπ i p r
  let h := fiberwiseRestriction_isPullback p i r
  refine ⟨?_⟩
  rw [← h.isoPullback_hom_snd]
  exact leftFibrations.comp_mem _ _ (MorphismProperty.of_isIso _ h.isoPullback.hom)
    (leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := r.π)))

/-- 概要：left anodyne な形状制限は定値底の全空間間の自明 Kan fibration。
方針：相対内部 Hom の全境界の持ち上げを底変換する。
規約：元の形状制限そのもの。使われ方：始点固定の path の相対充填。 -/
lemma fiberwiseFunctorRestriction_trivialKanFibration {A K E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (i : A ⟶ K) (hi : leftAnodyneExtensions i) :
    TrivialKanFibration (fiberwiseFunctorRestriction p i) := by
  let r := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := trivialKanFibration_relativeHom_of_leftAnodyne i hi p r
  let h := fiberwiseRestriction_isPullback p i r
  refine ⟨?_⟩
  rw [← h.isoPullback_hom_snd]
  exact trivialKanFibrations.comp_mem _ _ (MorphismProperty.of_isIso _ h.isoPullback.hom)
    (trivialKanFibrations.pullback_snd _ _ (TrivialKanFibration.mem (p := r.π)))

end SerrePositivity.InfinityCategories.F2

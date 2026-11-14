module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseRestrictionPullback

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：単射な形状制限は定値底の全空間間の left fibration。
方針：相対内部 Hom の left fibration 性を底変換し、元の制限射に同型で戻す。
規約：元の底を保持。使われ方：path の両端を同時に固定する持ち上げ。 -/
instance fiberwiseFunctorRestriction_leftFibration {A K E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : A ⟶ K) [Mono i] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p i) := by
  let r := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_pullbackObjObjπ i p r
  let h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseRestriction_isPullback p i r
  refine ⟨?_⟩
  rw [← h.isoPullback_hom_snd]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _ (MorphismProperty.of_isIso _ h.isoPullback.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := r.π)))

/-- 概要：left anodyne な形状制限は定値底の全空間間の自明 Kan fibration。
方針：相対内部 Hom の全境界の持ち上げを底変換する。
規約：元の形状制限そのもの。使われ方：始点固定の path の相対充填。 -/
lemma fiberwiseFunctorRestriction_trivialKanFibration {A K E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : A ⟶ K) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorRestriction p i) := by
  let r := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne i hi p r
  let h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseRestriction_isPullback p i r
  refine ⟨?_⟩
  rw [← h.isoPullback_hom_snd]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ (MorphismProperty.of_isIso _ h.isoPullback.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := r.π)))

end SerrePositivity.InfinityCategories.Project.FilteredExchange

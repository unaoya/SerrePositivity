module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedTwistedProjectionExistence

/-!
概要：各段の twisted-arrow 引き戻しの weighted 全空間は、元の全空間の同じ引き戻し。
方針：元の二つの射影を保つ各次数の存在と一意性から、引き戻しの普遍性を証明する。
規約：充填性や filtered 性は不要。使われ方：共同 Hom の元の評価空間への厳密な移送。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)

/-- 元の全空間の両射影の四角形は、同じ底上の引き戻し。 -/
lemma weightedTwistedProjections_isPullback :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedBaseProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedTotalProjection F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationProjectionCocone F).ι) := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨n⟩⟩
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun q ↦ q.app (Opposite.op ⦋n⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedProjections_commute F)
  · intro x y h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedProjections_jointlyInjective F n
    exact Prod.ext h.1 h.2
  · intro t s h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedProjections_exists F t s h

/-- 元の twisted-arrow 引き戻しへの、元の両射影を持つ同じ全空間の同型。 -/
def weightedTwistedPullbackIso : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedElementsDiagram F) ≅
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationProjectionCocone F).ι) :=
  (weightedTwistedProjections_isPullback F).isoPullback

/-- 同じ同型の第一射影は、元の全 twisted arrow の底射影。 -/
lemma weightedTwistedPullbackIso_fst :
    (weightedTwistedPullbackIso F).hom ≫ pullback.fst _ _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedBaseProjection F :=
  (weightedTwistedProjections_isPullback F).isoPullback_hom_fst

/-- 同じ同型の第二射影は、元の weighted 全空間への元の射影。 -/
lemma weightedTwistedPullbackIso_snd :
    (weightedTwistedPullbackIso F).hom ≫ pullback.snd _ _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedTotalProjection F :=
  (weightedTwistedProjections_isPullback F).isoPullback_hom_snd

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

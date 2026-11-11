module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TwistedElementsBaseChange

/-!
概要：元の twisted-arrow 終点族の共同射影を、元の Hom 射影の引き戻しとして保持する。
方針：両射影を保つ構成済みの厳密な底変換同型を使う。
規約：元の射影のまま判定。使われ方：係数と始点への同じ復元射の底変換。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の twisted-arrow 終点族の共同射影は、同じ Hom 射影の厳密な引き戻し。 -/
lemma twistedElements_isPullback {E C : SSet.{u}} (p : E ⟶ C) :
    IsPullback (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsProjection p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsBaseMap p) :=
  IsPullback.of_iso_pullback ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsProjection_base p).symm⟩
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsBaseChangeIso p) (pullback.lift_fst _ _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsBaseChangeIso_projection p)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

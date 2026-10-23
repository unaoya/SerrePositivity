module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedElementsBaseChange

/-!
概要：元の twisted-arrow 終点族の共同射影を、元の Hom 射影の引き戻しとして保持する。
方針：両射影を保つ構成済みの厳密な底変換同型を使う。
規約：元の射影のまま判定。使われ方：係数と始点への同じ復元射の底変換。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の twisted-arrow 終点族の共同射影は、同じ Hom 射影の厳密な引き戻し。 -/
lemma twistedElements_isPullback {E C : SSet.{u}} (p : E ⟶ C) :
    IsPullback (pullback.fst (edgewiseRight C) p) (twistedElementsProjection p)
      (twistedArrowProjection C) (twistedElementsBaseMap p) :=
  IsPullback.of_iso_pullback ⟨(twistedElementsProjection_base p).symm⟩
    (twistedElementsBaseChangeIso p) (pullback.lift_fst _ _ _)
    (twistedElementsBaseChangeIso_projection p)

end SerrePositivity.InfinityCategories.F2.Ind

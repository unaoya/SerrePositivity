module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.PushoutCotensor

/-! # The original pushout gives an actual pullback of internal Hom objects -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.PushoutInternalHomPullback
variable {A B C P : SSet.{v}} {i : A ⟶ B} {j : A ⟶ C} {u : B ⟶ P} {g : C ⟶ P}

lemma isPullback (sq : IsPushout i j u g) (K : SSet.{v}) :
    IsPullback ((pre u).app K) ((pre g).app K) ((pre i).app K) ((pre j).app K) := by
  have hw : (pre u).app K ≫ (pre i).app K = (pre g).app K ≫ (pre j).app K := by
    rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map, sq.w]
  apply IsPullback.of_isLimit' ⟨hw⟩
  refine PullbackCone.IsLimit.mk _
    (fun c => PushoutCotensor.glue sq c.fst c.snd c.condition)
    (fun c => PushoutCotensor.glue_left _ _ _ _) (fun c => PushoutCotensor.glue_right _ _ _ _)
    (fun c m hm hn => ?_)
  exact PushoutCotensor.hom_ext sq
    (hm.trans (PushoutCotensor.glue_left _ _ _ _).symm)
    (hn.trans (PushoutCotensor.glue_right _ _ _ _).symm)

end SerrePositivity.SimplicialModel.PushoutInternalHomPullback

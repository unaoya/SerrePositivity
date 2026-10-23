module
public import SerrePositivity.InfinityCategories.Derived.Gluing.StrictPathPullbackMap
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalPullbackInputFibration

/-! 二段の区間引き戻しと、同じ全 path・二入力を持つ一段の引き戻しの厳密同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
variable {A B Q : SSet.{u}} (f : A ⟶ Q) (g : B ⟶ Q)

lemma dgGluingIntervalPathCoordinates_isPullback :
    IsPullback (F2.intervalPullbackPath f g) (F2.intervalPullbackInputPair f g)
      (F2.arrowEndpointPair Q) (f ⊗ₘ g) := by
  have hh : lift (fst A B ≫ f) (snd A B ≫ g) = f ⊗ₘ g := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [lift_fst, lift_snd, tensorHom_fst, tensorHom_snd]
  simpa only [hh] using F2.intervalPullbackInputPair_isPullback f g

def dgGluingIntervalPathCoordinatesIso : F2.intervalPullback f g ≅
    pullback (F2.arrowEndpointPair Q) (f ⊗ₘ g) :=
  (dgGluingIntervalPathCoordinates_isPullback f g).isoPullback

lemma dgGluingIntervalPathCoordinatesIso_path :
    (dgGluingIntervalPathCoordinatesIso f g).hom ≫ pullback.fst _ _ =
      F2.intervalPullbackPath f g :=
  (dgGluingIntervalPathCoordinates_isPullback f g).isoPullback_hom_fst

lemma dgGluingIntervalPathCoordinatesIso_inputs :
    (dgGluingIntervalPathCoordinatesIso f g).hom ≫ pullback.snd _ _ =
      F2.intervalPullbackInputPair f g :=
  (dgGluingIntervalPathCoordinates_isPullback f g).isoPullback_hom_snd

end SerrePositivity.InfinityCategories

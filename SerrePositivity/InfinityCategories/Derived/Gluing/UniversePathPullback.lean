module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KanIntervalPathTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseIntervalHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePullbacks

/-! 通常の係数 path 引き戻しを、同じ区間と端点番号を保って共通宇宙へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopyLimits
open scoped Simplicial

lemma dgGluingUliftIntervalEndpointPair (K : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).map (F2.arrowEndpointPair K) ≫
        (uliftTensorIso K K).hom =
      (uliftIntervalHomIso.{u, v} K).hom ≫
        F2.arrowEndpointPair ((SSet.uliftFunctor.{v, u}).obj K) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, F2.arrowEndpointPair, lift_fst,
      uliftIntervalHomIso_hom_evaluate]
    rfl
  · simp only [Category.assoc, F2.arrowEndpointPair, lift_snd,
      uliftIntervalHomIso_hom_evaluate]
    rfl

variable {K T : SSet.{u}} (a : T ⟶ K ⊗ K)

lemma dgGluingUliftPathPullback_isPullback :
    IsPullback
      ((SSet.uliftFunctor.{v, u}).map (pullback.fst (F2.arrowEndpointPair K) a) ≫
        (uliftIntervalHomIso.{u, v} K).hom)
      ((SSet.uliftFunctor.{v, u}).map (pullback.snd (F2.arrowEndpointPair K) a))
      (F2.arrowEndpointPair ((SSet.uliftFunctor.{v, u}).obj K))
      ((SSet.uliftFunctor.{v, u}).map a ≫ (uliftTensorIso K K).hom) := by
  refine ((IsPullback.of_hasPullback (F2.arrowEndpointPair K) a).map
    (SSet.uliftFunctor.{v, u})).of_iso (Iso.refl _) (uliftIntervalHomIso K)
      (Iso.refl _) (uliftTensorIso K K) ?_ ?_ ?_ ?_
  · simp
  · simp
  · exact dgGluingUliftIntervalEndpointPair K
  · simp

def dgGluingUliftPathPullbackIso :
    (SSet.uliftFunctor.{v, u}).obj (pullback (F2.arrowEndpointPair K) a) ≅
      pullback (F2.arrowEndpointPair ((SSet.uliftFunctor.{v, u}).obj K))
        ((SSet.uliftFunctor.{v, u}).map a ≫ (uliftTensorIso K K).hom) :=
  (dgGluingUliftPathPullback_isPullback.{u, v} a).isoPullback

lemma dgGluingUliftPathPullbackIso_path :
    (dgGluingUliftPathPullbackIso.{u, v} a).hom ≫ pullback.fst _ _ =
      (SSet.uliftFunctor.{v, u}).map (pullback.fst (F2.arrowEndpointPair K) a) ≫
        (uliftIntervalHomIso.{u, v} K).hom :=
  (dgGluingUliftPathPullback_isPullback.{u, v} a).isoPullback_hom_fst

lemma dgGluingUliftPathPullbackIso_inputs :
    (dgGluingUliftPathPullbackIso.{u, v} a).hom ≫ pullback.snd _ _ =
      (SSet.uliftFunctor.{v, u}).map (pullback.snd (F2.arrowEndpointPair K) a) :=
  (dgGluingUliftPathPullback_isPullback.{u, v} a).isoPullback_hom_snd

end SerrePositivity.InfinityCategories

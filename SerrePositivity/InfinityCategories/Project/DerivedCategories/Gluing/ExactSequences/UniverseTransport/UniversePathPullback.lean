module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.KanIntervalPathTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.UniverseIntervalHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.UniversePullbacks

/-! 通常の係数 path 引き戻しを、同じ区間と端点番号を保って共通宇宙へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

open scoped _root_.Simplicial

lemma dgGluingUliftIntervalEndpointPair (K : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K K).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso.{u, v} K).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair ((SSet.uliftFunctor.{v, u}).obj K) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, lift_fst,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso_hom_evaluate]
    rfl
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, lift_snd,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso_hom_evaluate]
    rfl

variable {K T : SSet.{u}} (a : T ⟶ K ⊗ K)

lemma dgGluingUliftPathPullback_isPullback :
    IsPullback
      ((SSet.uliftFunctor.{v, u}).map (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) a) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso.{u, v} K).hom)
      ((SSet.uliftFunctor.{v, u}).map (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair ((SSet.uliftFunctor.{v, u}).obj K))
      ((SSet.uliftFunctor.{v, u}).map a ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K K).hom) := by
  refine ((IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) a).map
    (SSet.uliftFunctor.{v, u})).of_iso (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso K)
      (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K K) ?_ ?_ ?_ ?_
  · simp
  · simp
  · exact dgGluingUliftIntervalEndpointPair K
  · simp

def dgGluingUliftPathPullbackIso :
    (SSet.uliftFunctor.{v, u}).obj (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) a) ≅
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair ((SSet.uliftFunctor.{v, u}).obj K))
        ((SSet.uliftFunctor.{v, u}).map a ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso K K).hom) :=
  (dgGluingUliftPathPullback_isPullback.{u, v} a).isoPullback

lemma dgGluingUliftPathPullbackIso_path :
    (dgGluingUliftPathPullbackIso.{u, v} a).hom ≫ pullback.fst _ _ =
      (SSet.uliftFunctor.{v, u}).map (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) a) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso.{u, v} K).hom :=
  (dgGluingUliftPathPullback_isPullback.{u, v} a).isoPullback_hom_fst

lemma dgGluingUliftPathPullbackIso_inputs :
    (dgGluingUliftPathPullbackIso.{u, v} a).hom ≫ pullback.snd _ _ =
      (SSet.uliftFunctor.{v, u}).map (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair K) a) :=
  (dgGluingUliftPathPullback_isPullback.{u, v} a).isoPullback_hom_snd

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

module

public import SerrePositivity.KST.Spectra.D3UniversalLoopModelCorrection
public import SerrePositivity.KST.Spectra.D3StageStructureCoherenceCriterion

/-!
概要：保持した段模型比較と単位を、同じ全入力の普遍模型比較・単位へ戻す。
方針：元の終点入力の前合成と、元の同じ実模型接続の厳密回収を使う。
規約：補正の恒等性は仮定しない。使われ方：全段の補正を一つの実二方向模型へ還元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3UniversalStageSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 保持した元の段模型比較は、同じ全入力比較の元の終点入力による前合成。 -/
lemma commonChosenStageLoopImageComparison_section (n : ℕ) :
    HEq (commonChosenStageLoopImageComparison.{u} n)
      (d3DoubleEndpointLoopImageComparison.{u}.precomp
        (commonChosenStageLoopDiagramFamily (n + 1) ≫
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) := by
  let g := commonChosenStageLoopDiagramFamily.{u} (n + 1) ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1
  let c := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointLoopImageComparison.precomp g)
    (commonChosenStageLoopedCanonicalFamily_section n)
    (commonChosenStageCanonicalImageFamily_section n)
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq
    (commonChosenStageLoopedCanonicalFamily_section n).symm
    (commonChosenStageCanonicalImageFamily_section n).symm rfl
    c (commonChosenStageCanonicalImageDoubleEndpointIso n)
    (d3DoubleEndpointLoopImageComparison.precomp g)
    (d3CanonicalImageLeftDiagramIso.precomp g)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, d3DoubleEndpointLoopImageComparison_recover] at h
  have hc : c ≪≫ commonChosenStageCanonicalImageDoubleEndpointIso n =
      commonChosenStageLoopedCanonicalDoubleEndpointIso n :=
    eq_of_heq (h.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm)
  rw [commonChosenStageLoopImageComparison_doubleEndpoint] at hc
  have he := congrArg (fun e ↦ e ≪≫
    (commonChosenStageCanonicalImageDoubleEndpointIso n).symm) hc
  have he' : c = commonChosenStageLoopImageComparison n := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using he
  exact (heq_of_eq he'.symm).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)

/-- 元の段 canonical image 単位も、同じ全入力単位の同じ終点入力による前合成。 -/
lemma commonChosenStageCanonicalImageUnitIso_section (n : ℕ) :
    HEq (commonChosenStageCanonicalImageUnitIso.{u} n)
      (d3CanonicalImageUnitIso.{u}.precomp
        (commonChosenStageLoopDiagramFamily (n + 1) ≫
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) := by
  unfold commonChosenStageCanonicalImageUnitIso d3CanonicalImageUnitIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans ?_
  refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_precomp_heq _ _ _ _).symm
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp]
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq
  rw [commonChosenStageLoopImageFamily_corner]

private lemma symm_heq {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hf : f = f') (hg : g = g')
    (h : HEq e' e) : HEq e'.symm e.symm := by
  subst f' g'
  cases eq_of_heq h
  rfl

/-- 保持した各段の模型補正は、同じ全入力補正の同じ終点入力による前合成。 -/
lemma commonChosenStageLoopModelCorrection_section (n : ℕ) :
    HEq (commonChosenStageLoopModelCorrection.{u} n)
      (d3DoubleEndpointLoopModelCorrection.{u}.precomp
        (commonChosenStageLoopDiagramFamily (n + 1) ≫
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) := by
  let g := commonChosenStageLoopDiagramFamily.{u} (n + 1) ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1
  have hs : g ≫ (pointedKanLoopInfinity ≫ pointedKanLoopInfinity) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet
        (d3StageKanEnriched.{u} (n + 2))).comp SSet pointedKanLoopEnrichedFunctor).comp
          SSet pointedKanLoopEnrichedFunctor) := by
    rw [← Category.assoc, commonChosenStageLoopTarget_enriched,
      commonChosenStageCanonicalLoopSource_enriched]
  have hl : g ≫ (d3LoopedSectionFamily ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
      commonChosenStageLoopedCanonicalFamily n ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0 := by
    rw [← Category.assoc, commonChosenStageLoopedCanonicalFamily_section]
  have hr : g ≫ ((pointedKanLoopInfinity ≫ d3PointedKanLoopSection) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
      commonChosenStageCanonicalImageFamily n ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0 := by
    rw [← Category.assoc, commonChosenStageCanonicalImageFamily_section]
  have hc := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq
    (d3DoubleEndpointLoopImageComparison.precomp g) (commonChosenStageLoopImageComparison n)
    (commonChosenStageLoopedCanonicalFamily_section n)
    (commonChosenStageCanonicalImageFamily_section n)
    (commonChosenStageLoopImageComparison_section n)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp] at hc
  have huc := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq hs hl hr
    (d3LoopedSectionUnitIso.precomp g)
    ((d3DoubleEndpointLoopImageComparison.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)).precomp g)
    (commonChosenStageLoopedCanonicalUnitIso n)
    ((commonChosenStageLoopImageComparison n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (commonChosenStageLoopedCanonicalUnitIso_section n) hc
  have hw := symm_heq (d3CanonicalImageUnitIso.precomp g)
    (commonChosenStageCanonicalImageUnitIso n) hs hr
    (commonChosenStageCanonicalImageUnitIso_section n)
  unfold commonChosenStageLoopModelCorrection d3DoubleEndpointLoopModelCorrection
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm]
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq hs hr hs _ _ _ _ huc hw

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

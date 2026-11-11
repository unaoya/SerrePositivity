module

public import SerrePositivity.KST.Spectra.D3CommonStageRefinedPasting

/-!
概要：同じ次段 refined／実始点比較の通常 loop 像を、指定三角形として回収する。
方針：既存三角形全体を loop で写し、四頂点だけを元の実 loop 像の端点へ正規化する。
規約：保持した模型間比較と loop 始点表示を同一視しない。
使われ方：BF 全体へ持ち上げる際に残る、同じ段比較の構造整合の正確な検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3LoopedTriangleSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

lemma commonChosenStageRefinedLoopSource_enriched (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (commonRefinedStageKanEnriched.{u} (n + 1)) ≫ pointedKanLoopInfinity =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonRefinedStageKanEnriched (n + 1)).comp
        SSet pointedKanLoopEnrichedFunctor) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  rfl

lemma commonChosenStageCanonicalLoopSource_enriched (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonOriginalEnriched.comp SSet (d3StageKanEnriched.{u} (n + 2))).comp
      SSet pointedKanLoopEnrichedFunctor) ≫ pointedKanLoopInfinity =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 2))).comp
      SSet pointedKanLoopEnrichedFunctor).comp SSet pointedKanLoopEnrichedFunctor) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  rfl

/-- 元の同じ次段の標準始点表示同型の通常 loop 像。 -/
def commonChosenStageLoopedCanonicalUnitIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet
      (d3StageKanEnriched.{u} (n + 2))).comp SSet pointedKanLoopEnrichedFunctor).comp
        SSet pointedKanLoopEnrichedFunctor))
      (commonChosenStageLoopedCanonicalFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((commonChosenStageCanonicalUnitIso (n + 1)).postcomp pointedKanLoopInfinity)
    (commonChosenStageCanonicalLoopSource_enriched n)
    (commonChosenStageLoopedCanonicalFamily_corner n 0 0).symm

/-- 同じ既存の次段 refined／実始点比較へ通常 loop を施した値。 -/
def commonChosenStageLoopedRefinedSourceIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonRefinedStageKanEnriched.{u} (n + 1)).comp
      SSet pointedKanLoopEnrichedFunctor))
      (commonChosenStageLoopImageFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((commonChosenStageRefinedSourceNormalizedIso (n + 1)).postcomp
    pointedKanLoopInfinity) (commonChosenStageRefinedLoopSource_enriched n)
      (commonChosenStageLoopImageFamily_corner n 0 0).symm

private lemma commonStageLoopedCanonicalDiagram_source (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      (((commonChosenStageCanonicalDiagramIso.{u} (n + 1)).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)).postcomp pointedKanLoopInfinity)
      (commonChosenStageLoopImageFamily_corner n 0 0).symm
      (commonChosenStageLoopedCanonicalFamily_corner n 0 0).symm =
    (commonChosenStageLoopedCanonicalDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) := by
  have h := commonChosenStageLoopedCanonicalDiagramIso_corner n 0 0
  have hc := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp (commonChosenStageCanonicalDiagramIso (n + 1))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) pointedKanLoopInfinity
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans
    ((heq_of_eq hc).trans h.symm))

private lemma commonStageLoopedProjection_normalized (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((commonProjectionStructureQIso.{u} (n + 1)).postcomp pointedKanLoopInfinity)
      (commonChosenStageRefinedLoopSource_enriched n)
      (commonChosenStageCanonicalLoopSource_enriched n) = commonProjectionStructureLoopQIso n := by
  have h : HEq ((commonProjectionStructureQIso (n + 1)).postcomp pointedKanLoopInfinity)
      ((commonStageLoopFunctorIso (n + 1)).postcomp pointedKanLoopInfinity) := by
    unfold commonProjectionStructureQIso
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _
  unfold commonProjectionStructureLoopQIso
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans
    (h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm))

/-- 同じ次段の比較三角形の通常 loop 像は、元の同じ右射影 loop 像と表示同型を回収する。 -/
lemma commonChosenStageLoopedRefinedSource_triangle (n : ℕ) :
    commonChosenStageLoopedRefinedSourceIso.{u} n ≪≫
      (commonChosenStageLoopedCanonicalDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    commonProjectionStructureLoopQIso n ≪≫ commonChosenStageLoopedCanonicalUnitIso n := by
  have h := congrArg (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e pointedKanLoopInfinity)
    (commonChosenStageRefinedSourceNormalized_triangle (n + 1))
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans] at h
  have hn := d3FunctorIso_square_transport _ _ _ _
    (commonChosenStageRefinedLoopSource_enriched n)
    (commonChosenStageLoopImageFamily_corner n 0 0).symm
    (commonChosenStageCanonicalLoopSource_enriched n)
    (commonChosenStageLoopedCanonicalFamily_corner n 0 0).symm h
  rw [commonStageLoopedCanonicalDiagram_source, commonStageLoopedProjection_normalized] at hn
  exact hn

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

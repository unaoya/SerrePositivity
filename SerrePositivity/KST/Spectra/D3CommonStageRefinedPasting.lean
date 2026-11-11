module

public import SerrePositivity.KST.Spectra.D3CommonStageTargetStructure

/-!
概要：元の refined／実始点の同じ段比較を、保持した模型間比較の始点成分へ接続する。
方針：既存の指定三角形を端点だけ正規化し、右射影構造正方形との貼合せ式へ代入する。
規約：比較を選び直さない。模型間比較の始点成分を恒等とは扱わない。
使われ方：BF 全体の図式比較へ進むための、同じ既存段比較の構造貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3RefinedPastingSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の同じ refined／実始点比較の、実段図式を保持する端点表示。 -/
def commonChosenStageRefinedSourceNormalizedIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (commonRefinedStageKanEnriched.{u} n))
      (commonChosenStageLoopDiagramFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (commonChosenStageRefinedSourceIso n)
    (by rw [commonRefinedStageKanEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp])
    (commonChosenStageLoopDiagramFamily_source n).symm

private lemma commonStageSourceCanonical_normalized (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (commonChosenStageSourceCanonicalIso.{u} n)
      (commonChosenStageLoopDiagramFamily_source n).symm rfl =
    (commonChosenStageCanonicalDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) := by
  unfold commonChosenStageSourceCanonicalIso
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _))

private lemma commonStageEndpointLoop_normalized (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (commonChosenStageEndpointLoopIso.{u} n)
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (commonRefinedStageKanEnriched n) from by
          rw [commonRefinedStageKanEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp])
      (commonChosenStageLoopTarget_enriched n) = commonProjectionStructureQIso n := by
  have h : HEq (commonChosenStageEndpointLoopIso n) (commonStageLoopFunctorIso n) := by
    unfold commonChosenStageEndpointLoopIso
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _
  unfold commonProjectionStructureQIso
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans
    (h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm))

/-- 元の同じ段比較と全図式始点比較の三角形は、指定右射影の同じ表示同型に一致する。 -/
lemma commonChosenStageRefinedSourceNormalized_triangle (n : ℕ) :
    commonChosenStageRefinedSourceNormalizedIso.{u} n ≪≫
      (commonChosenStageCanonicalDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    commonProjectionStructureQIso n ≪≫ commonChosenStageCanonicalUnitIso n := by
  have h := d3FunctorIso_square_transport
    (commonChosenStageRefinedSourceIso n) (commonChosenStageSourceCanonicalIso n)
    (commonChosenStageEndpointLoopIso n)
    (d3PointedKanLoopSection_sourceIso.precomp
      (commonChosenStageLoopDiagramFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (commonRefinedStageKanEnriched n) from by
        rw [commonRefinedStageKanEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp])
    (commonChosenStageLoopDiagramFamily_source n).symm
    (commonChosenStageLoopTarget_enriched n) rfl
    (commonChosenStageRefinedSourceIso_canonical_triangle n)
  rw [commonStageSourceCanonical_normalized, commonStageEndpointLoop_normalized] at h
  exact h

/-- この端点正規化した同じ既存段比較は、指定三角形を逆向きに解いた値そのもの。 -/
lemma commonChosenStageRefinedSourceNormalized_factorization (n : ℕ) :
    commonChosenStageRefinedSourceNormalizedIso.{u} n =
      (commonProjectionStructureQIso n ≪≫ commonChosenStageCanonicalUnitIso n) ≪≫
        ((commonChosenStageCanonicalDiagramIso n).postcomp
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)).symm := by
  let a := commonChosenStageRefinedSourceNormalizedIso.{u} n
  let d := (commonChosenStageCanonicalDiagramIso.{u} n).postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
  calc
    _ = (a ≪≫ d) ≪≫ d.symm := by
      simp only [a, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = _ := by rw [commonChosenStageRefinedSourceNormalized_triangle]

/-- 元の同じ段比較・BF 構造・次段比較の loop 像・保持した模型比較の一体の貼合せ。 -/
lemma commonChosenStageRefinedSourceNormalized_pasting (n : ℕ) :
    ((commonChosenStageRefinedSourceNormalizedIso.{u} n ≪≫
      (commonChosenStageStructureDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) ≪≫
      (commonChosenStageLoopedCanonicalDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) ≪≫
      (commonChosenStageLoopImageComparison n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    (commonProjectionStructureRefinedIso n ≪≫ commonProjectionStructureLoopQIso n) ≪≫
      commonChosenStageCanonicalImageUnitIso n := by
  rw [commonChosenStageRefinedSourceNormalized_factorization]
  exact commonChosenStageRefinedLoopImage_pasting n

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

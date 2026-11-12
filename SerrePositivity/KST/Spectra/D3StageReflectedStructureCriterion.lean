module

public import SerrePositivity.KST.Spectra.D3StageLoopReflectedComparison
public import SerrePositivity.KST.Spectra.D3StageStructureCoherenceCriterion

/-!
概要：転置した実模型比較の単位整合と、反転を保持する BF 段構造の整合を結ぶ。
方針：同じ次段図式比較に反転の自然性を適用し、既証の指定貼合せへ代入する。
規約：単位整合の実証を仮定なしの値として供給しない。B の実値は未完成。
使われ方：正しい補正を保つ比較の、幾何的に証明すべき単位三角形を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3ReflectedCriterionSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 転置した実全図式比較の始点を、元の厳密な始点表示へ正規化する。 -/
def commonChosenStageLoopReflectedSourceIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonChosenStageLoopedCanonicalFamily.{u} n ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
      (commonChosenStageCanonicalImageFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((commonChosenStageLoopReflectedComparison n).postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (by rw [Category.assoc, d3LoopDiagramTranspose_corner]) rfl

lemma commonChosenStageLoopReflectedSourceIso_eq (n : ℕ) :
    commonChosenStageLoopReflectedSourceIso.{u} n =
    ((d3LoopDiagramReflection d3PointedKanLoopSection
      d3PointedKanLoopSection_target).precomp (commonChosenStageLoopedCanonicalFamily n)).symm ≪≫
      (commonChosenStageLoopImageComparison n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  commonChosenStageLoopReflectedComparison_source n

/-- 転置済み模型の単位三角形は、同じ比較に実次段像の反転を保持する構造条件と同値。
右辺の三角形自体は未証明であり、この判定で BF 全体の比較を供給したとは扱わない。 -/
lemma commonChosenStageRefinedSource_reflected_structure_iff (n : ℕ) :
    (commonChosenStageRefinedSourceNormalizedIso.{u} n ≪≫
      (commonChosenStageStructureDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    commonProjectionStructureRefinedIso n ≪≫
      (commonChosenStageLoopedRefinedSourceIso n ≪≫ commonChosenStageImageReflection n)) ↔
    commonChosenStageLoopedCanonicalUnitIso.{u} n ≪≫
      commonChosenStageLoopReflectedSourceIso n = commonChosenStageCanonicalImageUnitIso n := by
  let ρ := (d3LoopDiagramReflection d3PointedKanLoopSection
    d3PointedKanLoopSection_target).precomp (commonChosenStageLoopedCanonicalFamily.{u} n)
  have hρ : ρ ≪≫ ρ = Iso.refl _ := by
    have h := congrArg (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e
      (commonChosenStageLoopedCanonicalFamily.{u} n))
      (d3LoopDiagramReflection_involution d3PointedKanLoopSection
        d3PointedKanLoopSection_target)
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans] at h
    have hr : (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity.{u} 0 0)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) from Iso.refl _).precomp
          (commonChosenStageLoopedCanonicalFamily n) = Iso.refl _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
      exact Functor.mapIso_refl _ _
    rw [hr] at h
    exact h
  have hρsymm : ρ.symm = ρ := by
    have h := congrArg (fun e ↦ ρ.symm ≪≫ e) hρ
    simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans, Iso.trans_refl] using h.symm
  have hd := d3LoopDiagramReflection_naturality d3PointedKanLoopSection
    d3PointedKanLoopSection_target (commonChosenStageLoopedCanonicalDiagramIso.{u} n)
  change (commonChosenStageLoopedCanonicalDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) ≪≫ ρ =
    commonChosenStageImageReflection n ≪≫
      (commonChosenStageLoopedCanonicalDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) at hd
  have ht : (commonChosenStageLoopedRefinedSourceIso.{u} n ≪≫ commonChosenStageImageReflection n) ≪≫
      (commonChosenStageLoopedCanonicalDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
      commonProjectionStructureLoopQIso n ≪≫
        (commonChosenStageLoopedCanonicalUnitIso n ≪≫ ρ) := by
    rw [Iso.trans_assoc, ← hd, ← Iso.trans_assoc,
      commonChosenStageLoopedRefinedSource_triangle, Iso.trans_assoc]
  have h := d3Iso_pasting_coherence_iff
    (commonChosenStageRefinedSourceNormalizedIso.{u} n)
    ((commonChosenStageStructureDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (commonProjectionStructureRefinedIso n)
    (commonChosenStageLoopedRefinedSourceIso n ≪≫ commonChosenStageImageReflection n)
    (commonProjectionStructureLoopQIso n) (commonChosenStageLoopedCanonicalUnitIso n ≪≫ ρ)
    ((commonChosenStageLoopedCanonicalDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    ((commonChosenStageLoopImageComparison n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (commonChosenStageCanonicalImageUnitIso n)
    (commonChosenStageRefinedSourceNormalized_pasting n) ht
  rw [commonChosenStageLoopReflectedSourceIso_eq]
  change _ ↔ commonChosenStageLoopedCanonicalUnitIso n ≪≫
    (ρ.symm ≪≫ _) = _
  rw [hρsymm, ← Iso.trans_assoc]
  simpa only [Iso.trans_assoc] using h

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

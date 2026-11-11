module

public import SerrePositivity.KST.Spectra.D3LoopCanonicalSectionTransport
public import SerrePositivity.KST.Spectra.D3StageStructureTail

/-!
概要：実 loop 図式の厳密 tail 終点にある構造同型を、同じ元の次段 BF 構造へ戻す。
方針：元の指定構造同型の tail 前合成と標準図式 transport の切断表示を接続する。
規約：円交換因子を比較しない。標準模型間比較を恒等として消去しない。
使われ方：元の右射影の構造正方形を実段図式の標準比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3TargetStructureSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 同じ実次段 loop 像の厳密終点は、元の同じ次々段評価の通常 loop 作用。 -/
lemma commonChosenStageLoopImageFamily_target_next (n : ℕ) :
    commonChosenStageLoopImageFamily.{u} n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
      (commonOriginalInfinityMap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched (n + 2))) ≫
        pointedKanLoopInfinity := by
  rw [commonChosenStageLoopImageFamily_corner, commonChosenStageLoopDiagramFamily_target_next]

/-- 実段図式の同じ厳密終点の通常 loop を、元の豊穣関手の端点表示へ戻す。 -/
lemma commonChosenStageLoopTarget_enriched (n : ℕ) :
    (commonChosenStageLoopDiagramFamily.{u} n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫
      pointedKanLoopInfinity =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 1))).comp
      SSet pointedKanLoopEnrichedFunctor) := by
  rw [commonChosenStageLoopDiagramFamily_target_next,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  rfl

/-- 同じ実次段像の終点の通常 loop も、元の同じ二重 loop 豊穣作用へ戻る。 -/
lemma commonChosenStageLoopImageLoopTarget_enriched (n : ℕ) :
    (commonChosenStageLoopImageFamily.{u} n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫
      pointedKanLoopInfinity =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 2))).comp
      SSet pointedKanLoopEnrichedFunctor).comp SSet pointedKanLoopEnrichedFunctor) := by
  rw [commonChosenStageLoopImageFamily_target_next,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  rfl

/-- 実図式の構造同型の厳密終点は、元の同じ次段構造同型への前合成。 -/
lemma commonChosenStageStructureDiagramIso_target_next (n : ℕ) :
    HEq ((commonChosenStageStructureDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      ((d3StageStructureFunctorIso (n + 1)).precomp commonOriginalInfinityMap) := by
  have h0 := commonChosenStageStructureDiagramIso_target n
  have hc := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp (d3StageStructureFunctorIso n)
    nativeTail commonOriginalInfinityMap
  have hn : HEq ((d3StageStructureFunctorIso n).precomp commonNativeLoopEndpoint)
      (((d3StageStructureFunctorIso n).precomp nativeTail).precomp commonOriginalInfinityMap) :=
    heq_of_eq hc.symm
  have ht := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_precomp_heq ((d3StageStructureFunctorIso n).precomp nativeTail)
    (d3StageTail n)
    (show nativeTail ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched (n + 1)) ≫
      pointedKanLoopInfinity) = _ from by rw [← Category.assoc, d3StageTail])
    commonOriginalInfinityMap
  have he := congrArg (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e commonOriginalInfinityMap)
    (d3StageStructureTailFunctorIso_eq n)
  exact h0.trans (hn.trans (ht.symm.trans (heq_of_eq he)))

/-- 同じ厳密終点構造の通常 loop 像は、元の右射影構造正方形の同じ上辺。 -/
lemma commonChosenStageStructureDiagramIso_target_loop (n : ℕ) :
    HEq (((commonChosenStageStructureDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).postcomp pointedKanLoopInfinity)
      (((d3StageStructureFunctorIso (n + 1)).precomp commonOriginalInfinityMap).postcomp
        pointedKanLoopInfinity) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq
    ((d3StageStructureFunctorIso (n + 1)).precomp commonOriginalInfinityMap)
    ((commonChosenStageStructureDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    (commonChosenStageLoopDiagramFamily_target_next n).symm
    (by rw [commonChosenStageLoopImageFamily_target_next, Category.assoc])
    (commonChosenStageStructureDiagramIso_target_next n) pointedKanLoopInfinity

/-- 同じ実図式終点構造の loop 像を、元の右射影正方形の厳密端点で表示する。 -/
def commonChosenStageTargetLoopStructureIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonOriginalEnriched.comp SSet
      (d3StageKanEnriched.{u} (n + 1))).comp SSet pointedKanLoopEnrichedFunctor))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 2))).comp
        SSet pointedKanLoopEnrichedFunctor).comp SSet pointedKanLoopEnrichedFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (((commonChosenStageStructureDiagramIso n).postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).postcomp pointedKanLoopInfinity)
    (commonChosenStageLoopTarget_enriched n) (commonChosenStageLoopImageLoopTarget_enriched n)

/-- 実図式の同じ厳密終点の構造同型を、元の右射影正方形の指定値として回収する。 -/
lemma commonChosenStageTargetLoopStructureIso_eq (n : ℕ) :
    commonChosenStageTargetLoopStructureIso.{u} n = commonProjectionStructureOriginalIso n := by
  unfold commonChosenStageTargetLoopStructureIso commonProjectionStructureOriginalIso
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans
    ((commonChosenStageStructureDiagramIso_target_loop n).trans
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm))

/-- 同じ実段図式の終点構造を、元の右射影の構造正方形に保持して接続する。 -/
lemma commonChosenStageTargetLoopStructure_square (n : ℕ) :
    commonProjectionStructureQIso.{u} n ≪≫ commonChosenStageTargetLoopStructureIso n =
      commonProjectionStructureRefinedIso n ≪≫ commonProjectionStructureLoopQIso n := by
  rw [commonChosenStageTargetLoopStructureIso_eq]
  exact commonProjectionStructureIso_square n

/-- 標準図式の始点表示同型は、同じ実終点構造の指定 transport と交換する。 -/
lemma commonChosenStageCanonicalStructure_source_loop (n : ℕ) :
    ((commonChosenStageStructureDiagramIso.{u} n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).postcomp pointedKanLoopInfinity ≪≫
      d3PointedKanLoopSection_sourceIso.precomp
        (commonChosenStageLoopImageFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) =
    d3PointedKanLoopSection_sourceIso.precomp
        (commonChosenStageLoopDiagramFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≪≫
      (commonChosenStageCanonicalStructureIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  d3LoopCanonicalTransport_source_naturality d3PointedKanLoopSection
    d3PointedKanLoopSection_target d3PointedKanLoopSection_sourceIso
      (commonChosenStageStructureDiagramIso n)

/-- 同じ厳密終点から標準図式始点への表示同型を、元の右射影の端点で保持する。 -/
def commonChosenStageCanonicalUnitIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonOriginalEnriched.comp SSet
      (d3StageKanEnriched.{u} (n + 1))).comp SSet pointedKanLoopEnrichedFunctor))
      (commonChosenStageCanonicalFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3PointedKanLoopSection_sourceIso.precomp
    (commonChosenStageLoopDiagramFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    (commonChosenStageLoopTarget_enriched n) (by simp only [commonChosenStageCanonicalFamily,
      Category.assoc])

/-- 同じ次段像の厳密終点から標準図式始点への表示同型の、元の二重 loop 端点での値。 -/
def commonChosenStageCanonicalImageUnitIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet
      (d3StageKanEnriched.{u} (n + 2))).comp SSet pointedKanLoopEnrichedFunctor).comp
        SSet pointedKanLoopEnrichedFunctor))
      (commonChosenStageCanonicalImageFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3PointedKanLoopSection_sourceIso.precomp
    (commonChosenStageLoopImageFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    (commonChosenStageLoopImageLoopTarget_enriched n)
    (by simp only [commonChosenStageCanonicalImageFamily, d3LoopCanonicalFamily, Category.assoc])

/-- 同じ標準始点表示と実終点構造の交換則を、元の右射影の厳密端点で保持する。 -/
lemma commonChosenStageCanonicalUnit_structure (n : ℕ) :
    commonChosenStageTargetLoopStructureIso.{u} n ≪≫ commonChosenStageCanonicalImageUnitIso n =
      commonChosenStageCanonicalUnitIso n ≪≫
        (commonChosenStageCanonicalStructureIso n).postcomp
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) := by
  exact d3FunctorIso_square_transport _ _ _ _
    (commonChosenStageLoopTarget_enriched n) (commonChosenStageLoopImageLoopTarget_enriched n)
    rfl rfl (commonChosenStageCanonicalStructure_source_loop n)

/-- 同じ右射影構造正方形と標準図式の始点表示は、一つの全関手正方形に接続する。 -/
lemma commonChosenStageCanonicalRefinedStructure_square (n : ℕ) :
    (commonProjectionStructureQIso.{u} n ≪≫ commonChosenStageCanonicalUnitIso n) ≪≫
      (commonChosenStageCanonicalStructureIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    (commonProjectionStructureRefinedIso n ≪≫ commonProjectionStructureLoopQIso n) ≪≫
      commonChosenStageCanonicalImageUnitIso n := by
  calc
    _ = commonProjectionStructureQIso n ≪≫
        (commonChosenStageTargetLoopStructureIso n ≪≫
          commonChosenStageCanonicalImageUnitIso n) := by
      rw [Iso.trans_assoc, ← commonChosenStageCanonicalUnit_structure]
    _ = (commonProjectionStructureQIso n ≪≫ commonChosenStageTargetLoopStructureIso n) ≪≫
        commonChosenStageCanonicalImageUnitIso n := by rw [Iso.trans_assoc]
    _ = _ := by rw [commonChosenStageTargetLoopStructure_square]

/-- 元の右射影・構造・既存段比較を、保持した模型間比較の始点成分まで一体で接続する。 -/
lemma commonChosenStageRefinedLoopImage_pasting (n : ℕ) :
    ((((commonProjectionStructureQIso.{u} n ≪≫ commonChosenStageCanonicalUnitIso n) ≪≫
        ((commonChosenStageCanonicalDiagramIso n).postcomp
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)).symm) ≪≫
      (commonChosenStageStructureDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) ≪≫
      (commonChosenStageLoopedCanonicalDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) ≪≫
      (commonChosenStageLoopImageComparison n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    (commonProjectionStructureRefinedIso n ≪≫ commonProjectionStructureLoopQIso n) ≪≫
      commonChosenStageCanonicalImageUnitIso n := by
  let a := commonProjectionStructureQIso.{u} n ≪≫ commonChosenStageCanonicalUnitIso n
  let d := (commonChosenStageCanonicalDiagramIso.{u} n).postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
  let g := (commonChosenStageCanonicalStructureIso.{u} n).postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
  let s := (commonChosenStageStructureDiagramIso.{u} n).postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
  let l := (commonChosenStageLoopedCanonicalDiagramIso.{u} n).postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
  let c := (commonChosenStageLoopImageComparison.{u} n).postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
  have h : d ≪≫ g = (s ≪≫ l) ≪≫ c := commonChosenStageLoopImageComparison_source n
  calc
    _ = a ≪≫ (d.symm ≪≫ ((s ≪≫ l) ≪≫ c)) := by
      simp only [a, d, s, l, c, Iso.trans_assoc]
    _ = a ≪≫ (d.symm ≪≫ (d ≪≫ g)) := by rw [← h]
    _ = a ≪≫ g := by simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
    _ = _ := commonChosenStageCanonicalRefinedStructure_square n

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

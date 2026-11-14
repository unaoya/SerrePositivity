module

public import SerrePositivity.KST.Spectra.D3CommonStageProjection
public import SerrePositivity.KST.Spectra.D3CommonLoopDiagramResolution
public import SerrePositivity.KST.SConstruction.PointedKanLoopInfinity
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：共通 BF 右射影の各段の標的を、元の点つき Kan loop ∞ 関手に照合する。
方針：内部 Hom の元の豊穣作用を同じ閉合成の curry へ移す。
規約：円交換因子は比較しない。各段の全関手比較を BF 全体の比較とは数えない。
使われ方：d3b② の補助標的と実 loop 図式の段比較の接続端。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3StageLoopSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance d3StageLoopPointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

/-- 二つの段 loop 作用は、元の同じ豊穣 Hom の全単体で厳密一致する。 -/
lemma d3Stage_loop_action (X Y : PointedKanObject.{u}) :
    (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map X.obj Y.obj =
      pointedKanLoopEnrichedFunctor.map X Y := by
  change (PointedMapping.ihomAction PointedSimplicialSet.circle.{u} X.obj Y.obj).right =
    (pointedLoopHom X.obj Y.obj).right
  rw [PointedMapping.ihomAction_eq_curry_comp]
  rfl

/-- 補助標的の段作用は、元の次段評価へ実 loop を施した同じ豊穣関手。 -/
lemma commonTargetStageKanEnriched_eq_loop (n : ℕ) :
    commonTargetStageKanEnriched.{u} n =
      (commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 1))).comp SSet
        pointedKanLoopEnrichedFunctor := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro X
    apply ObjectProperty.FullSubcategory.ext
    change PointedObject.basedHom PointedSimplicialSet.circle (X.val.level (n + 1)).space = _
    rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  change commonBaseMap X.val Y.val ≫
      (fullOriginalMap X.val Y.val ≫ evaluation X.val Y.val (n + 1) ≫
        (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map
          (X.val.level (n + 1)).space (Y.val.level (n + 1)).space) =
    ((commonBaseMap X.val Y.val ≫ fullOriginalMap X.val Y.val) ≫
      evaluation X.val Y.val (n + 1)) ≫ pointedKanLoopEnrichedFunctor.map
        ((d3StageKanEnriched (n + 1)).obj X.val) ((d3StageKanEnriched (n + 1)).obj Y.val)
  rw [← d3Stage_loop_action]
  simp only [Category.assoc]
  rfl

/-- 元の共通右射影を成分として、共通 BF 対象の段と元の次段の loop を全関手比較。 -/
def commonStageLoopFunctorIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))
      ((commonOriginalInfinityMap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched (n + 1))) ≫
        pointedKanLoopInfinity) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (commonStageProjectionFunctorIso n)
    (by rw [commonRefinedStageKanEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp])
    (by
      rw [commonTargetStageKanEnriched_eq_loop, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
      rfl)

/-- 同じ全実 loop 図式を記憶する基底上でも、元の右射影の段比較を保持する。
記憶した図式始点との比較は、この段比較とは別に証明する。 -/
def commonLoopDiagramStageLoopIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonLoopDiagramRefinedMap.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))
      (((commonLoopDiagramProjection ≫ commonOriginalInfinityMap) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched (n + 1))) ≫ pointedKanLoopInfinity) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (commonStageLoopFunctorIso.{u} n) commonLoopDiagramProjection
  simpa only [commonLoopDiagramRefinedMap, Category.assoc] using e

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

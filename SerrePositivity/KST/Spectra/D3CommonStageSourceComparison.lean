module

public import SerrePositivity.KST.Spectra.D3PointedKanLoopSection
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：同じ共通 BF 実 loop 図式の段始点作用と、元の共通 refined 段作用を全関手比較する。
方針：元の厳密終点を保つ loop 図式の全関手同型と、元の右射影の段自然同型を合成する。
規約：全頂点一致からは推論しない。段をまたぐ BF 構造の自然性は別工程。
使われ方：d3b② の実図式始点と共通 BF 全 Hom の比較を BF 全体へ接続する入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3SourceComparisonSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 同じ厳密終点を持つ、元の標準 loop 切断による全図式族。 -/
def commonChosenStageCanonicalFamily (n : ℕ) :
    SimplicialNerve CommonObject.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  (commonChosenStageLoopDiagramFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫
    d3PointedKanLoopSection

/-- 同じ標準全図式族の厳密終点は、元の実段図式族の終点そのもの。 -/
lemma commonChosenStageCanonicalFamily_target (n : ℕ) :
    commonChosenStageCanonicalFamily.{u} n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
      commonChosenStageLoopDiagramFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 := by
  rw [commonChosenStageCanonicalFamily, Category.assoc,
    d3PointedKanLoopSection_target, Category.comp_id]

/-- 元の厳密終点を保つ、実段図式族から同じ標準族への既存型の全図式比較。 -/
def commonChosenStageCanonicalDiagramIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonChosenStageLoopDiagramFamily.{u} n) (commonChosenStageCanonicalFamily n) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramFamilyIso_of_section d3PointedKanLoopSection d3PointedKanLoopSection_target
    (commonChosenStageLoopDiagramFamily n) (commonChosenStageCanonicalFamily n)
    (commonChosenStageCanonicalFamily_target n).symm

/-- 同じ実段図式族の始点と、その同じ厳密終点の通常 loop の全関手比較。 -/
def commonChosenStageSourceLoopIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonChosenLoopSource ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched.{u} n))
      ((commonChosenStageLoopDiagramFamily n ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫ pointedKanLoopInfinity) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((commonChosenStageCanonicalDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (commonChosenStageLoopDiagramFamily_source n) rfl ≪≫
      (d3PointedKanLoopSection_sourceIso.precomp
        (commonChosenStageLoopDiagramFamily n ≫
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).symm

/-- 同じ元の共通 refined 段と、同じ実 loop 図式始点段の全関手同型。
各段をまたぐ BF 構造整合や BF 全体の自然同型とは区別する。 -/
def commonChosenStageRefinedSourceIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched.{u} n))
      (commonChosenLoopSource ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n)) :=
  commonChosenStageEndpointLoopIso n ≪≫ (commonChosenStageSourceLoopIso n).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

module

public import SerrePositivity.KST.Spectra.D3LoopCanonicalNaturality

/-!
概要：元の BF 構造同型と、同じ実段図式から標準図式への比較の自然な正方形。
方針：既存の構造同型の指定終点値を持ち上げ、実 fiber 比較の自然性へ代入する。
規約：次段 loop 像の比較と次段比較の loop 像の同定は別工程。BF 全体の自然同型と数えない。
使われ方：refined／実始点段比較の、指定構造射を保つ段間整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 同じ次段 loop 像と厳密終点を共有する標準全図式族。 -/
def commonChosenStageCanonicalImageFamily (n : ℕ) :
    SimplicialNerve CommonObject.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  d3LoopCanonicalFamily d3PointedKanLoopSection (commonChosenStageLoopImageFamily n)

/-- 元の段間構造の終点同型そのものを持ち上げた、標準全図式間の指定同型。 -/
def commonChosenStageCanonicalStructureIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonChosenStageCanonicalFamily.{u} n)
      (commonChosenStageCanonicalImageFamily n) :=
  d3LoopCanonicalTransport d3PointedKanLoopSection d3PointedKanLoopSection_target
    (commonChosenStageStructureDiagramIso n)

/-- 同じ次段 loop 像から、その同じ終点の標準族への実 fiber 内比較。 -/
def commonChosenStageCanonicalImageDiagramIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonChosenStageLoopImageFamily.{u} n)
      (commonChosenStageCanonicalImageFamily n) :=
  d3LoopCanonicalDiagramIso d3PointedKanLoopSection d3PointedKanLoopSection_target
    (commonChosenStageLoopImageFamily n)

/-- 既存の実段図式比較は、元の BF 構造同型と指定終点の持ち上げに厳密に自然。 -/
lemma commonChosenStageCanonicalStructure_naturality (n : ℕ) :
    commonChosenStageCanonicalDiagramIso.{u} n ≪≫ commonChosenStageCanonicalStructureIso n =
      commonChosenStageStructureDiagramIso n ≪≫ commonChosenStageCanonicalImageDiagramIso n :=
  d3LoopCanonicalDiagramIso_naturality d3PointedKanLoopSection d3PointedKanLoopSection_target
    (commonChosenStageStructureDiagramIso n)

/-- 同じ全図式の自然な構造正方形は、実始点の比較でも同じ値を保つ。 -/
lemma commonChosenStageCanonicalStructure_source (n : ℕ) :
    (commonChosenStageCanonicalDiagramIso.{u} n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) ≪≫
      (commonChosenStageCanonicalStructureIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    (commonChosenStageStructureDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) ≪≫
      (commonChosenStageCanonicalImageDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) := by
  have h := congrArg (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
      (commonChosenStageCanonicalStructure_naturality n)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans] using h

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

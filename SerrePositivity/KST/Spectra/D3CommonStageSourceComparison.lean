module

public import SerrePositivity.KST.Spectra.D3PointedKanLoopSection

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

/-- 同じ実段図式族の始点と、その同じ厳密終点の通常 loop の全関手比較。 -/
def commonChosenStageSourceLoopIso (n : ℕ) :
    FunctorIso (commonChosenLoopSource ≫ coherentNerveMap (d3StageKanEnriched.{u} n))
      ((commonChosenStageLoopDiagramFamily n ≫
        loopDiagramEvaluation PointedKanInfinity 1 1) ≫ pointedKanLoopInfinity) := by
  let T := commonChosenStageLoopDiagramFamily.{u} n ≫
    loopDiagramEvaluation PointedKanInfinity 1 1
  let G := T ≫ d3PointedKanLoopSection
  have ht : commonChosenStageLoopDiagramFamily n ≫
      loopDiagramEvaluation PointedKanInfinity 1 1 =
        G ≫ loopDiagramEvaluation PointedKanInfinity 1 1 := by
    dsimp only [G]
    rw [Category.assoc, d3PointedKanLoopSection_target, Category.comp_id]
  have e := loopDiagramFamilyIso_of_section d3PointedKanLoopSection
    d3PointedKanLoopSection_target (commonChosenStageLoopDiagramFamily n) G ht
  have es := e.postcomp (loopDiagramEvaluation PointedKanInfinity 0 0)
  rw [commonChosenStageLoopDiagramFamily_source] at es
  have eu := (d3PointedKanLoopSection_sourceIso.precomp T).symm
  change FunctorIso (G ≫ loopDiagramEvaluation PointedKanInfinity 0 0)
    (T ≫ pointedKanLoopInfinity) at eu
  exact es ≪≫ eu

/-- 同じ元の共通 refined 段と、同じ実 loop 図式始点段の全関手同型。
各段をまたぐ BF 構造整合や BF 全体の自然同型とは区別する。 -/
def commonChosenStageRefinedSourceIso (n : ℕ) :
    FunctorIso (coherentNerveMap commonRefinedEnriched ≫
      coherentNerveMap (d3StageKanEnriched.{u} n))
      (commonChosenLoopSource ≫ coherentNerveMap (d3StageKanEnriched n)) :=
  commonChosenStageEndpointLoopIso n ≪≫ (commonChosenStageSourceLoopIso n).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

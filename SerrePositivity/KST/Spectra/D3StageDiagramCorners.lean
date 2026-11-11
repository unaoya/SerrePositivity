module

public import SerrePositivity.KST.Spectra.D3StageDiagramProjection
public import SerrePositivity.KST.Spectra.D3FunctorIsoEvaluation

/-!
概要：実 loop 全図式の段間同型の四つの角を、元の BF 構造射の同じ値として回収する。
方針：端点正規化・充満忠実な逆像・内部 Hom への作用の指定値保持を順に合成する。
規約：自由な成分同型を選び直さず、既存の構造同型そのものを評価する。
使われ方：refined 段比較の両側の構造射と実全図式の構造射の照合。
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
local instance d3DiagramCornersSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 同じ全四角形構造同型の各角は、元の同じ BF 構造同型への前合成。 -/
lemma commonChosenStageStructureSquareIso_corner (n : ℕ) (i j : Fin 2) :
    HEq ((commonChosenStageStructureSquareIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := PointedKanInfinity)
        (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)))
      ((d3StageStructureFunctorIso n).precomp
        ((commonChosenLoopDiagramFamily ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp)
              (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))) := by
  dsimp only [commonChosenStageStructureSquareIso]
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans
    (d3FunctorIsoMapPost_evaluate_precomp _ _ _)

/-- 実 loop 全図式へ回収した同じ構造同型も、各角で元の BF 構造同型を回収する。 -/
lemma commonChosenStageStructureDiagramIso_corner (n : ℕ) (i j : Fin 2) :
    HEq ((commonChosenStageStructureDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j))
      ((d3StageStructureFunctorIso n).precomp
        ((commonChosenLoopDiagramFamily ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp)
              (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))) := by
  let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
  let ev := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]))
    (Y := PointedKanInfinity)
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq (commonChosenStageStructureSquareIso n)
    ((commonChosenStageStructureDiagramIso n).postcomp ι)
    (commonChosenStageLoopDiagramFamily_ι n).symm
    (commonChosenStageLoopImageFamily_ι n).symm
    (commonChosenStageStructureDiagramIso_projection n) ev
  have hc := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp (commonChosenStageStructureDiagramIso n) ι ev
  exact (heq_of_eq hc.symm).trans (h.trans (commonChosenStageStructureSquareIso_corner n i j))


/-- 同じ全図式構造同型の実始点は、元の始点関手の BF 構造同型そのもの。 -/
lemma commonChosenStageStructureDiagramIso_source (n : ℕ) :
    HEq ((commonChosenStageStructureDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
      ((d3StageStructureFunctorIso n).precomp commonChosenLoopSource) := by
  have h := commonChosenStageStructureDiagramIso_corner.{u} n 0 0
  have hm : ((commonChosenLoopDiagramFamily ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      commonChosenLoopSource := by
    exact Category.assoc _ _ _
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq (d3StageStructureFunctorIso n) hm)

/-- 同じ全図式構造同型の厳密終点は、元の nativeTail 終点の BF 構造同型そのもの。 -/
lemma commonChosenStageStructureDiagramIso_target (n : ℕ) :
    HEq ((commonChosenStageStructureDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      ((d3StageStructureFunctorIso n).precomp commonNativeLoopEndpoint) := by
  have h := commonChosenStageStructureDiagramIso_corner.{u} n 1 1
  have hm : ((commonChosenLoopDiagramFamily ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
      commonNativeLoopEndpoint := by
    exact (Category.assoc _ _ _).trans commonChosenLoopDiagramFamily_target
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq (d3StageStructureFunctorIso n) hm)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

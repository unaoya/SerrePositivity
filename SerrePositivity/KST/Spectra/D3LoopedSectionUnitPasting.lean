module

public import SerrePositivity.KST.Spectra.D3LoopedSectionComparisonCorners
public import SerrePositivity.KST.Spectra.D3StageLoopedUnitTriangle

/-!
概要：元の切断の同じ始点単位を loop 像の比較へ貼り、元の端点模型単位を厳密回収。
方針：切断補正の始点での逆と順比較を全関手空間で打ち消し、元の段単位へ接続する。
規約：単位や比較を選び直さない。保持した模型補正との一致は別工程。
使われ方：既存の looped canonical 単位を二方向実模型の指定始点へ移す。
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

/-- 元の端点図式の loop 像の各角は、同じ元の角の通常 loop 像。 -/
lemma d3EndpointLoopImageFamily_corner (i j : Fin 2) :
    d3EndpointLoopImageFamily.{u} ≫ loopDiagramEvaluation PointedKanInfinity i j =
      (d3PointedKanEndpointLoopDiagram ≫ loopDiagramEvaluation PointedKanInfinity i j) ≫
        pointedKanLoopInfinity := by
  dsimp only [loopDiagramEvaluation]
  rw [← Category.assoc, d3EndpointLoopImageFamily_ι, Category.assoc,
    d3SquareEvaluation_postcomp]
  rw [← d3PointedKanEndpointLoopDiagram_ι]
  simp only [Category.assoc]

/-- 元の厳密切断の始点単位へ通常 loop を施し、同じ loop 像の厳密始点へ接続。 -/
def d3LoopedSectionUnitIso :
    FunctorIso (pointedKanLoopInfinity.{u} ≫ pointedKanLoopInfinity)
      (d3LoopedSectionFamily ≫ loopDiagramEvaluation PointedKanInfinity 0 0) :=
  F2.functorIsoOfEq (d3PointedKanLoopSection_sourceIso.postcomp pointedKanLoopInfinity)
    rfl (d3LoopedSectionFamily_corner 0 0).symm

/-- 元の切断単位と同じ切断補正の loop 像を貼ると、元の端点模型単位を回収する。 -/
lemma d3LoopedSectionUnitIso_pasting :
    F2.functorIsoOfEq (d3LoopedSectionUnitIso.{u} ≪≫
      d3LoopedSectionDiagramIso.postcomp (loopDiagramEvaluation PointedKanInfinity 0 0))
      rfl (d3EndpointLoopImageFamily_corner 0 0) =
    d3PointedKanEndpointLoopDiagram_sourceIso.postcomp pointedKanLoopInfinity := by
  have hbase : d3PointedKanLoopSection_sourceIso.{u} ≪≫
      d3PointedKanLoopSection_diagramIso.postcomp (loopDiagramEvaluation PointedKanInfinity 0 0) =
      d3PointedKanEndpointLoopDiagram_sourceIso := by
    dsimp only [d3PointedKanLoopSection_sourceIso]
    rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  have hloop := congrArg (fun e ↦ FunctorIso.postcomp e pointedKanLoopInfinity) hbase
  rw [F2.functorIso_postcomp_trans] at hloop
  have hp := functorIso_trans_heq_of_heq rfl (d3LoopedSectionFamily_corner 0 0).symm
    (d3EndpointLoopImageFamily_corner 0 0).symm
    (d3PointedKanLoopSection_sourceIso.postcomp pointedKanLoopInfinity)
    ((d3PointedKanLoopSection_diagramIso.postcomp
      (loopDiagramEvaluation PointedKanInfinity 0 0)).postcomp pointedKanLoopInfinity)
    d3LoopedSectionUnitIso
    (d3LoopedSectionDiagramIso.postcomp (loopDiagramEvaluation PointedKanInfinity 0 0))
    (F2.functorIsoOfEq_heq _ _ _) (d3LoopedSectionDiagramIso_corner 0 0)
  exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans (hp.trans (heq_of_eq hloop)))

/-- 保持済み段模型の looped canonical 単位は、同じ切断 loop 単位の元の終点前合成。 -/
lemma commonChosenStageLoopedCanonicalUnitIso_section (n : ℕ) :
    HEq (commonChosenStageLoopedCanonicalUnitIso.{u} n)
      (d3LoopedSectionUnitIso.precomp (commonChosenStageLoopDiagramFamily (n + 1) ≫
        loopDiagramEvaluation PointedKanInfinity 1 1)) := by
  unfold commonChosenStageLoopedCanonicalUnitIso
  refine (F2.functorIsoOfEq_heq _ _ _).trans ?_
  unfold commonChosenStageCanonicalUnitIso
  refine (functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  refine (heq_of_eq (F2.functorIso_precomp_postcomp d3PointedKanLoopSection_sourceIso
    (commonChosenStageLoopDiagramFamily (n + 1) ≫
      loopDiagramEvaluation PointedKanInfinity 1 1) pointedKanLoopInfinity)).trans ?_
  exact (functorIsoOfEq_precomp_heq _ _ _ _).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

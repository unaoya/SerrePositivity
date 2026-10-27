module

public import SerrePositivity.KST.Spectra.D3SectionUnitFaceComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoSelfUnitExchange

/-!
概要：元の単位比較と loop 始点表示の自然性を、指定単位面の始点上で厳密に貼る。
方針：全関手空間の前後合成交換と、元の全図式比較の同じ値を使用する。
規約：単位・切断・実面比較を選び直さない。使われ方：二方向模型接続の終点照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 元の単位比較の通常 loop 像を、元の厳密始点表示で保持する。 -/
def d3PointedKanUnitLoopIso :
    FunctorIso pointedKanLoopInfinity.{u}
      (coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})) ≫
        pointedKanLoopInfinity) :=
  F2.functorIsoOfEq (FunctorIso.postcomp d3PointedKanUnitFunctorIso.{u}.symm
    pointedKanLoopInfinity) (Category.id_comp _) rfl

/-- 元の単位内部 Hom 入力に対する同じ始点表示を、同じ実面の厳密始点へ正規化。 -/
def d3PointedKanUnitLoopSourceIso :
    FunctorIso (coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})) ≫
      pointedKanLoopInfinity)
      ((coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})) ≫
        d3PointedKanLoopSection) ≫ loopDiagramEvaluation PointedKanInfinity 0 0) :=
  F2.functorIsoOfEq (d3PointedKanLoopSection_sourceIso.precomp
    (coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u}))))
    rfl (Category.assoc _ _ _).symm

/-- 切断への単位比較の後合成の始点は、元の始点評価への同じ後合成。 -/
lemma d3PointedKanUnitSectionIso_source_value :
    HEq (d3PointedKanUnitSectionIso.{u}.postcomp
      (loopDiagramEvaluation PointedKanInfinity 0 0))
      (FunctorIso.postcomp d3PointedKanUnitFunctorIso.{u}.symm
        (d3PointedKanLoopSection ≫ loopDiagramEvaluation PointedKanInfinity 0 0)) := by
  unfold d3PointedKanUnitSectionIso
  refine (functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  exact heq_of_eq (F2.functorIso_postcomp_postcomp d3PointedKanUnitFunctorIso.{u}.symm
    d3PointedKanLoopSection (loopDiagramEvaluation PointedKanInfinity 0 0))

/-- 同じ単位比較の始点表示だけを揃えると、元の切断後合成の始点に厳密一致。 -/
lemma d3PointedKanUnitSectionIso_source :
    F2.functorIsoOfEq (FunctorIso.postcomp d3PointedKanUnitFunctorIso.{u}.symm
      (d3PointedKanLoopSection ≫ loopDiagramEvaluation PointedKanInfinity 0 0))
      (Category.id_comp _) (Category.assoc _ _ _).symm =
    d3PointedKanUnitSectionIso.postcomp (loopDiagramEvaluation PointedKanInfinity 0 0) := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
    d3PointedKanUnitSectionIso_source_value.symm)

/-- 同じ単位比較と元の loop 始点単位は、指定実面上の全関手正方形を可換にする。 -/
lemma d3PointedKanUnitLoop_source_square :
    d3PointedKanUnitLoopIso.{u} ≪≫ d3PointedKanUnitLoopSourceIso =
    d3PointedKanLoopSection_sourceIso ≪≫ d3PointedKanUnitSectionIso.postcomp
      (loopDiagramEvaluation PointedKanInfinity 0 0) := by
  have h := d3FunctorIso_square_transport
    (FunctorIso.postcomp d3PointedKanUnitFunctorIso.{u}.symm pointedKanLoopInfinity)
    (d3PointedKanLoopSection_sourceIso.precomp
      (coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})) ))
    (d3PointedKanLoopSection_sourceIso.precomp (𝟙 PointedKanInfinity))
    (FunctorIso.postcomp d3PointedKanUnitFunctorIso.{u}.symm
      (d3PointedKanLoopSection ≫ loopDiagramEvaluation PointedKanInfinity 0 0))
    (Category.id_comp _) rfl (Category.id_comp _) (Category.assoc _ _ _).symm
    (F2.functorIso_whisker_exchange d3PointedKanUnitFunctorIso.{u}.symm
      d3PointedKanLoopSection_sourceIso)
  rw [d3PointedKanUnitSectionIso_source] at h
  simpa only [F2.functorIso_precomp_id, d3PointedKanUnitLoopIso,
    d3PointedKanUnitLoopSourceIso, F2.functorIsoOfEq] using h

/-- 元の左単位面模型の始点比較を、同じ元の切断単位を使って保持する。 -/
def d3LeftUnitFaceSourceIso :
    FunctorIso (coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})) ≫
      pointedKanLoopInfinity)
      (d3DoubleEndpointLeftLoopFamily 1 1 ≫
        loopDiagramEvaluation PointedKanInfinity 0 0) :=
  d3KanLoopDiagramSourceIsoOverTarget (d3DoubleEndpointLeftLoopFamily 1 1) _
    (d3DoubleEndpointLeftTargetIso 1 1)

/-- 同じ実面始点比較は、同じ単位始点表示と元の指定模型比較の貼合せ。 -/
lemma d3LeftUnitFaceSourceIso_eq :
    d3LeftUnitFaceSourceIso.{u} = d3PointedKanUnitLoopSourceIso ≪≫
      (d3DoubleEndpointLeftModelIso 1 1).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0) := by
  have h := functorIso_trans_heq_of_heq rfl (Category.assoc _ _ _).symm rfl
    (d3PointedKanLoopSection_sourceIso.precomp
      (coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u}))))
    (F2.functorIsoOfEq ((d3DoubleEndpointLeftModelIso 1 1).postcomp
      (loopDiagramEvaluation PointedKanInfinity 0 0)) (Category.assoc _ _ _) rfl)
    d3PointedKanUnitLoopSourceIso
    ((d3DoubleEndpointLeftModelIso 1 1).postcomp (loopDiagramEvaluation PointedKanInfinity 0 0))
    (F2.functorIsoOfEq_heq _ _ _) (F2.functorIsoOfEq_heq _ _ _).symm
  exact eq_of_heq h.symm

/-- 単位面の全図式一致に元の loop 単位を貼ると、同じ端点単位・右単位比較を回収。 -/
lemma d3PointedKanUnitFace_source_triangle :
    d3PointedKanUnitLoopIso.{u} ≪≫ d3LeftUnitFaceSourceIso =
    d3PointedKanEndpointLoopDiagram_sourceIso ≪≫ d3EndpointRightUnitDiagramIso.postcomp
      (loopDiagramEvaluation PointedKanInfinity 0 0) := by
  have hs := congrArg (fun v ↦ FunctorIso.postcomp v
    (loopDiagramEvaluation PointedKanInfinity 0 0)) d3PointedKanSection_rightUnit_model.{u}
  rw [F2.functorIso_postcomp_trans, F2.functorIso_postcomp_trans] at hs
  have hc : d3PointedKanLoopSection_sourceIso.{u} ≪≫
      d3PointedKanLoopSection_diagramIso.postcomp (loopDiagramEvaluation PointedKanInfinity 0 0) =
      d3PointedKanEndpointLoopDiagram_sourceIso := by
    dsimp only [d3PointedKanLoopSection_sourceIso]
    rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  rw [d3LeftUnitFaceSourceIso_eq, ← Iso.trans_assoc, d3PointedKanUnitLoop_source_square,
    Iso.trans_assoc, ← hs, ← Iso.trans_assoc, hc]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

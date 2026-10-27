module

public import SerrePositivity.KST.Spectra.D3RetainedDoubleEndpointComparison

/-!
概要：canonical image 側の保持した始点単位を、同じ実右面の始点比較へ貼る。
方針：元の端点円表示と切断単位の全関手交換則を、指定模型比較と合成する。
規約：単位・模型比較を変更せず、円交換因子は比較しない。
使われ方：二つの始点表示の差を、同じ二方向実面比較上で照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 同じ通常 loop 入力の切断単位を、canonical image の厳密始点へ表示する。 -/
def d3CanonicalImageUnitIso :
    FunctorIso (pointedKanLoopInfinity.{u} ≫ pointedKanLoopInfinity)
      ((pointedKanLoopInfinity ≫ d3PointedKanLoopSection) ≫
        loopDiagramEvaluation PointedKanInfinity 0 0) :=
  F2.functorIsoOfEq (d3PointedKanLoopSection_sourceIso.precomp pointedKanLoopInfinity)
    rfl (Category.assoc _ _ _).symm

/-- 同じ端点円入力の切断単位を、実右面模型の厳密始点へ表示する。 -/
def d3EndpointCircleSectionUnitIso :
    FunctorIso (coherentNerveMap (d3PointedKanIhom endpointCircle.{u}) ≫
      pointedKanLoopInfinity)
      ((coherentNerveMap (d3PointedKanIhom endpointCircle) ≫ d3PointedKanLoopSection) ≫
        loopDiagramEvaluation PointedKanInfinity 0 0) :=
  F2.functorIsoOfEq (d3PointedKanLoopSection_sourceIso.precomp
    (coherentNerveMap (d3PointedKanIhom endpointCircle.{u})))
    rfl (Category.assoc _ _ _).symm

/-- 端点円表示を切断へ送った指定値は、始点でも同じ後合成値を保持する。 -/
lemma d3EndpointCircleSectionIso_source :
    F2.functorIsoOfEq (d3PointedKanEndpointLoopIso.{u}.postcomp
      (d3PointedKanLoopSection ≫ loopDiagramEvaluation PointedKanInfinity 0 0))
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm =
    (d3PointedKanEndpointLoopIso.postcomp d3PointedKanLoopSection).postcomp
      (loopDiagramEvaluation PointedKanInfinity 0 0) := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
    (heq_of_eq (F2.functorIso_postcomp_postcomp d3PointedKanEndpointLoopIso.{u}
      d3PointedKanLoopSection (loopDiagramEvaluation PointedKanInfinity 0 0))).symm)

/-- 元の端点円表示と切断単位は、canonical image の同じ始点正方形で可換。 -/
lemma d3CanonicalImageUnitIso_endpoint_square :
    d3PointedKanEndpointLoopIso.{u}.postcomp pointedKanLoopInfinity ≪≫
      d3EndpointCircleSectionUnitIso =
    d3CanonicalImageUnitIso ≪≫
      (d3PointedKanEndpointLoopIso.postcomp d3PointedKanLoopSection).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0) := by
  have h := d3FunctorIso_square_transport
    (d3PointedKanEndpointLoopIso.{u}.postcomp pointedKanLoopInfinity)
    (d3PointedKanLoopSection_sourceIso.precomp
      (coherentNerveMap (d3PointedKanIhom endpointCircle.{u})))
    (d3PointedKanLoopSection_sourceIso.precomp pointedKanLoopInfinity)
    (d3PointedKanEndpointLoopIso.postcomp
      (d3PointedKanLoopSection ≫ loopDiagramEvaluation PointedKanInfinity 0 0))
    rfl rfl (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
    (F2.functorIso_whisker_exchange d3PointedKanEndpointLoopIso.{u}
      d3PointedKanLoopSection_sourceIso)
  rw [d3EndpointCircleSectionIso_source] at h
  exact h

/-- 元の実右面の同じ始点比較を、元の実右面始点上に保持する。 -/
def d3RightDoubleEndpointSourceIso :
    FunctorIso (coherentNerveMap (d3PointedKanIhom endpointCircle.{u}) ≫
      pointedKanLoopInfinity)
      (d3DoubleEndpointRightLoopFamily 0 0 ≫ loopDiagramEvaluation PointedKanInfinity 0 0) :=
  d3KanLoopDiagramSourceIsoOverTarget _ _ (d3DoubleEndpointRightTargetIso 0 0)

/-- 実右面始点比較は、同じ切断単位と元の実右面模型比較の貼合せ。 -/
lemma d3RightDoubleEndpointSourceIso_eq :
    d3RightDoubleEndpointSourceIso.{u} = d3EndpointCircleSectionUnitIso ≪≫
      (d3DoubleEndpointRightModelIso 0 0).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0) := by
  have h := functorIso_trans_heq_of_heq rfl (Category.assoc _ _ _).symm rfl
    (d3PointedKanLoopSection_sourceIso.precomp
      (coherentNerveMap (d3PointedKanIhom endpointCircle.{u})))
    (F2.functorIsoOfEq ((d3DoubleEndpointRightModelIso 0 0).postcomp
      (loopDiagramEvaluation PointedKanInfinity 0 0)) (Category.assoc _ _ _) rfl)
    d3EndpointCircleSectionUnitIso
    ((d3DoubleEndpointRightModelIso 0 0).postcomp (loopDiagramEvaluation PointedKanInfinity 0 0))
    (F2.functorIsoOfEq_heq _ _ _) (F2.functorIsoOfEq_heq _ _ _).symm
  exact eq_of_heq h.symm

/-- canonical image の同じ単位を実模型接続へ貼ると、同じ端点単位・右実面比較を回収。 -/
lemma d3CanonicalImageLeftDiagramIso_unit_pasting :
    d3CanonicalImageUnitIso.{u} ≪≫
      d3CanonicalImageLeftDiagramIso.postcomp (loopDiagramEvaluation PointedKanInfinity 0 0) =
    d3PointedKanEndpointLoopIso.postcomp pointedKanLoopInfinity ≪≫
      d3RightDoubleEndpointSourceIso := by
  rw [d3CanonicalImageLeftDiagramIso, F2.functorIso_postcomp_trans,
    ← Iso.trans_assoc, ← d3CanonicalImageUnitIso_endpoint_square,
    Iso.trans_assoc, ← d3RightDoubleEndpointSourceIso_eq]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

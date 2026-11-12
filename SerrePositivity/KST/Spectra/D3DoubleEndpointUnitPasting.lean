module

public import SerrePositivity.KST.Spectra.D3LoopedSectionUnitPasting

/-!
概要：元の切断 loop 単位を二方向全図式比較へ貼り、指定実面の二重 loop 表示へ戻す。
方針：同じ切断補正の打消しと、同じ実面始点比較の角値を全関手空間で合成する。
規約：比較・単位を選び直さない。保持済み模型補正との一致は未証明。
使われ方：保持済みの looped canonical 段単位を実二方向模型へ移すための貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 元の端点模型単位の loop 像を、同じ実 loop 像の厳密始点へ正規化する。 -/
def d3EndpointLoopImageUnitIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pointedKanLoopInfinity.{u} ≫ pointedKanLoopInfinity)
      (d3EndpointLoopImageFamily ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3PointedKanEndpointLoopDiagram_sourceIso.postcomp pointedKanLoopInfinity)
    rfl (d3EndpointLoopImageFamily_corner 0 0).symm

/-- 元の切断単位と切断補正の loop 像の貼合せを、同じ実始点上で厳密に回収。 -/
lemma d3LoopedSectionUnitIso_pasting_eq :
    d3LoopedSectionUnitIso.{u} ≪≫
      d3LoopedSectionDiagramIso.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    d3EndpointLoopImageUnitIso := by
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ rfl
    (d3EndpointLoopImageFamily_corner 0 0)).symm.trans
      ((heq_of_eq d3LoopedSectionUnitIso_pasting).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm))

/-- 元の端点 loop 像の始点は、端点円作用の同じ通常 loop 像である。 -/
lemma d3EndpointLoopImageFamily_source :
    d3EndpointLoopImageFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom endpointCircle) ≫ pointedKanLoopInfinity := by
  rw [d3EndpointLoopImageFamily_corner, d3PointedKanEndpointLoopDiagram_corner]
  rfl

/-- 左実面の同じ始点比較を、元の実 loop 像と実右面の厳密始点上に表示する。 -/
def d3DoubleEndpointLeftImageSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3EndpointLoopImageFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
      (d3DoubleEndpointRightLoopFamily 0 0 ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointLeftSourceIso 0 0)
    d3EndpointLoopImageFamily_source.symm (d3DoubleEndpointRightLoopFamily_corner 0 0 0 0).symm

/-- 右実面の始点比較も、同じ loop 像と実左面の厳密始点へ表示を揃える。 -/
def d3DoubleEndpointRightImageSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3EndpointLoopImageFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
      (d3DoubleEndpointLeftLoopFamily 0 0 ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointRightSourceIso 0 0)
    d3EndpointLoopImageFamily_source.symm (d3DoubleEndpointLeftLoopFamily_corner 0 0 0 0).symm

/-- 左の全図式比較の始点は、同じ元の左実面始点比較そのもの。 -/
lemma d3DoubleEndpointLeftLoopImageDiagramIso_source :
    d3DoubleEndpointLeftLoopImageDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) = d3DoubleEndpointLeftImageSourceIso := by
  exact eq_of_heq ((d3DoubleEndpointLeftLoopImageDiagramIso_corner 0 0).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm)

/-- 右の全図式比較も、元の同じ指定始点比較を回収する。 -/
lemma d3DoubleEndpointRightLoopImageDiagramIso_source :
    d3DoubleEndpointRightLoopImageDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) = d3DoubleEndpointRightImageSourceIso := by
  exact eq_of_heq ((d3DoubleEndpointRightLoopImageDiagramIso_corner 0 0).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm)

/-- 切断 loop 単位を左二方向全図式比較へ貼ると、元の端点単位と左実面比較を回収。 -/
lemma d3LoopedSectionLeftDiagramIso_unit_pasting :
    d3LoopedSectionUnitIso.{u} ≪≫
      d3LoopedSectionLeftDiagramIso.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    d3EndpointLoopImageUnitIso ≪≫ d3DoubleEndpointLeftImageSourceIso := by
  rw [d3LoopedSectionLeftDiagramIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, ← Iso.trans_assoc,
    d3LoopedSectionUnitIso_pasting_eq, d3DoubleEndpointLeftLoopImageDiagramIso_source]

/-- 右二方向比較も、元の同じ単位と右実面比較の貼合せの指定値を保持。 -/
lemma d3LoopedSectionRightDiagramIso_unit_pasting :
    d3LoopedSectionUnitIso.{u} ≪≫
      d3LoopedSectionRightDiagramIso.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    d3EndpointLoopImageUnitIso ≪≫ d3DoubleEndpointRightImageSourceIso := by
  rw [d3LoopedSectionRightDiagramIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, ← Iso.trans_assoc,
    d3LoopedSectionUnitIso_pasting_eq, d3DoubleEndpointRightLoopImageDiagramIso_source]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

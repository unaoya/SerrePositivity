module

public import SerrePositivity.KST.Spectra.D3CanonicalImageUnitPasting

/-!
概要：looped canonical 側の単位貼合せを、canonical image 側と同じ実始点へ表示する。
方針：元の全図式比較と元の単位の同じ値だけを、厳密端点へ正規化する。
規約：円交換因子を直接比較せず、二方向実面の始点比較の差を保持する。
使われ方：保持した模型補正を同じ実始点上で検査する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 元の左実面始点比較を、同じ実右面の厳密始点へ表示する。 -/
def d3LeftDoubleEndpointSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom endpointCircle.{u}) ≫
      pointedKanLoopInfinity)
      (d3DoubleEndpointRightLoopFamily 0 0 ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointLeftSourceIso 0 0)
    rfl (d3DoubleEndpointRightLoopFamily_corner 0 0 0 0).symm

/-- 元の実 loop 像の同じ単位は、元の端点円表示の同じ loop 像を保持する。 -/
lemma d3EndpointLoopImageUnitIso_value :
    HEq d3EndpointLoopImageUnitIso.{u}
      (d3PointedKanEndpointLoopIso.{u}.postcomp pointedKanLoopInfinity) := by
  unfold d3EndpointLoopImageUnitIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans ?_
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq d3PointedKanEndpointLoopIso.{u}
    d3PointedKanEndpointLoopDiagram_sourceIso rfl
    (d3PointedKanEndpointLoopDiagram_corner 0 0).symm
    d3PointedKanEndpointSourceIso_value pointedKanLoopInfinity

/-- 左実面の始点表示を揃えても、元の同じ比較値を保持する。 -/
lemma d3DoubleEndpointLeftImageSourceIso_value :
    HEq d3DoubleEndpointLeftImageSourceIso.{u} d3LeftDoubleEndpointSourceIso.{u} := by
  unfold d3DoubleEndpointLeftImageSourceIso d3LeftDoubleEndpointSourceIso
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm

/-- looped canonical 側の同じ単位貼合せは、元の端点円表示と左実面始点比較を回収。 -/
lemma d3LoopedSectionLeftDiagramIso_unit_pasting_endpoint :
    d3LoopedSectionUnitIso.{u} ≪≫
      d3LoopedSectionLeftDiagramIso.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    d3PointedKanEndpointLoopIso.postcomp pointedKanLoopInfinity ≪≫
      d3LeftDoubleEndpointSourceIso := by
  rw [d3LoopedSectionLeftDiagramIso_unit_pasting]
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq rfl
    d3EndpointLoopImageFamily_source.symm rfl _ _ _ _
    d3EndpointLoopImageUnitIso_value d3DoubleEndpointLeftImageSourceIso_value)

/-- 同じ実右面の二方向始点比較の差を、同じ端点円 loop 入力上に保持する。 -/
def d3DoubleEndpointSourceDifference :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom endpointCircle.{u}) ≫
      pointedKanLoopInfinity)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom endpointCircle) ≫ pointedKanLoopInfinity) :=
  d3LeftDoubleEndpointSourceIso ≪≫ d3RightDoubleEndpointSourceIso.symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

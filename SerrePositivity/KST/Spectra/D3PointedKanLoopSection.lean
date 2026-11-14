module

public import SerrePositivity.KST.Spectra.D3PointedKanUnitIso
public import SerrePositivity.KST.Spectra.D3LoopDiagramTransport

/-!
概要：元の全端点 loop 図式と標準単位同型から、同じ Kan ∞ 圏上の厳密 loop 切断を作る。
方針：同じ指定単位同型の path を全図式の終点評価へ持ち上げ、元の図式との同型を保つ。
規約：通常 loop の全 Hom 作用を変更しない。安定性は仮定せず、ここからも結論しない。
使われ方：共通 BF 実段図式始点と通常の点つき loop の全関手比較。
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

/-- 元の実一点による pointed 条件。 -/
instance d3PointedKanInfinity_hasZero : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex PointedKanInfinity.{u} :=
  ⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex d3PointedKanPoint, d3PointedKanPoint_isZero⟩⟩

/-- 元の単位同型を、構成済み実 loop 図式族の終点に厳密に接続する。 -/
def d3PointedKanEndpointTargetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (𝟙 PointedKanInfinity.{u})
      (d3PointedKanEndpointLoopDiagram ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) := by
  rw [d3PointedKanEndpointLoopDiagram_corner]
  exact d3PointedKanUnitFunctorIso.symm

/-- 元の指定単位同型の path を保持した、同じ全 loop 図式族の終点補正。 -/
def d3PointedKanLoopCorrection :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pathCorrectedFunctorSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity.{u} 1 1)
    (d3LoopDiagramEvaluation_equivalenceLifting PointedKanInfinity)
    d3PointedKanEndpointLoopDiagram (𝟙 PointedKanInfinity) d3PointedKanEndpointTargetIso

/-- 元の全図式に指定単位同型だけを持ち上げた、厳密終点を持つ loop 切断。 -/
def d3PointedKanLoopSection : PointedKanInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  d3PointedKanLoopCorrection.map

/-- 終点は全 coherent 単体で元の恒等関手に厳密一致。 -/
lemma d3PointedKanLoopSection_target :
    d3PointedKanLoopSection.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
      𝟙 PointedKanInfinity := d3PointedKanLoopCorrection.comm

/-- 補正後も全四角形は、元の実端点パラメータ全図式に自然同型。 -/
def d3PointedKanLoopSection_diagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3PointedKanLoopSection.{u} d3PointedKanEndpointLoopDiagram :=
  d3PointedKanLoopCorrection.componentIso

/-- 厳密 loop 切断の始点作用も、元の通常点つき loop と全関手同型。 -/
def d3PointedKanLoopSection_sourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso pointedKanLoopInfinity.{u}
      (d3PointedKanLoopSection ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  d3PointedKanEndpointLoopDiagram_sourceIso ≪≫
    (d3PointedKanLoopSection_diagramIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)).symm

/-- 実 loop 図式の終点評価は、この実切断から全単射 RLP を持つ。 -/
lemma d3PointedKanLoopEvaluation_trivial :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity.{u} 1 1) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation_target_trivialKanFibration_of_section PointedKanInfinity
    d3PointedKanLoopSection d3PointedKanLoopSection_target

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

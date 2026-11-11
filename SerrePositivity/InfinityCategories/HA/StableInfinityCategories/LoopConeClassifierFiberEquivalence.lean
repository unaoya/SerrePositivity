module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeFixedApexDiagramFiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeClassifierInterval

/-!
概要：同じ実 loop 錐の図式 fiber 比較と、元の始点固定比較を同値として閉じる。
方針：同じ円柱の厳密な式を照合し、証明済みの実区間族の同値性を戻す。
規約：安定性や有限余極限を先取りしない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の loop 錐比較の実区間族を、同じ評価終点に厳密に正規化する。 -/
def loopConeFixedApexIntervalFamily {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) x ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌) t.diagramVertex) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square)) x
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)) x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)) x)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexComparison t x) ≫
      (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexComparison_endpoint t))).hom

/-- 同じ終点へ正規化した元の loop 錐比較の実区間族は同値。 -/
lemma loopConeFixedApexIntervalFamily_isQCatEquivalence {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (loopConeFixedApexIntervalFamily t x) :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexComparison_interval_isQCatEquivalence t x).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexComparison_endpoint t)))).isQCatEquivalence

/-- 既存の実 diagram fiber 比較は、厳密同型の下で同じ極限錐比較に一致する。 -/
lemma loopConeFixedApexDiagramFiberMap_interval {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexDiagramFiberIso t x).hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x t.diagramVertex ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberIntervalIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x t.diagramVertex).hom =
      loopConeFixedApexIntervalFamily t x := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalFamilyHomotopy_h_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy_precomp_h, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap_interval_h,
    loopConeFixedApexIntervalFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalFamilyHomotopy_eqToIso_target,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily_h]
  · rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexDiagramFiberIso_lift]
    conv_rhs =>
      arg 2
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneFamilyApex_eq_vertexEvaluation]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexComparison_ι]
    simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeApexComparisonHomotopy, Category.assoc]
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexComparison_endpoint t

/-- 指定された実 loop 四角形上の、既存の図式 fiber 比較そのものは同値。 -/
lemma loopConeClassifierDiagramFiberMap_isQCatEquivalence_of_loopSquare
    {X : SSet.{u}} [Quasicategory X] {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x t.diagramVertex) := by
  have hW := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexDiagramFiberIso t x)).isQCatEquivalence
  have hI := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberIntervalIso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x t.diagramVertex)).isQCatEquivalence
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexDiagramFiberIso t x).hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x t.diagramVertex ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberIntervalIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x
          t.diagramVertex).hom) := by
    rw [loopConeFixedApexDiagramFiberMap_interval]
    exact loopConeFixedApexIntervalFamily_isQCatEquivalence t x
  exact hI.cancel_right (hW.cancel_left h)

/-- 任意の実 loop 図式上で、既存の図式 fiber 比較そのものは同値。 -/
lemma loopConeClassifierDiagramFiberMap_isQCatEquivalence (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) (d : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x d) := by
  have h := loopConeClassifierDiagramFiberMap_isQCatEquivalence_of_loopSquare
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSquareOfDiagramVertex d) x
  exact Eq.mp (congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x v))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSquareOfDiagramVertex_diagramVertex d)) h

/-- 元の始点固定 loop 錐から comma への同じ実比較は同値。 -/
lemma loopConeClassifierSourceFiberMap_isQCatEquivalence (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap_isQCatEquivalence_of_diagramFibers X x
    (loopConeClassifierDiagramFiberMap_isQCatEquivalence X x)
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

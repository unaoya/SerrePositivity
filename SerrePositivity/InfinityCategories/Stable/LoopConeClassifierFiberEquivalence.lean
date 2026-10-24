module
public import SerrePositivity.InfinityCategories.Stable.LoopConeFixedApexDiagramFiber
public import SerrePositivity.InfinityCategories.Stable.LoopConeClassifierInterval

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
namespace SerrePositivity.InfinityCategories

/-- 元の loop 錐比較の実区間族を、同じ評価終点に厳密に正規化する。 -/
def loopConeFixedApexIntervalFamily {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    HomotopyLimits.fixedApexConeFamily (pullbackCospan t.square) x ⟶
      intervalMappingSpace x
        ((loopDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌) t.diagramVertex) :=
  terminalComparisonIntervalFamily (HomotopyLimits.coneFamilyApex (pullbackCospan t.square))
    ((sliceConeFamilyMap (pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) (pullbackCone t.square)) x
    (vertexFiberι (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)) x)
    (vertexFiberι_comp (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)) x)
    (loopConeFixedApexComparison t x) ≫
      (eqToIso (congrArg (intervalMappingSpace x) (loopConeFixedApexComparison_endpoint t))).hom

/-- 同じ終点へ正規化した元の loop 錐比較の実区間族は同値。 -/
lemma loopConeFixedApexIntervalFamily_isQCatEquivalence {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    IsQCatEquivalence (loopConeFixedApexIntervalFamily t x) :=
  (loopConeFixedApexComparison_interval_isQCatEquivalence t x).comp
    (qCatEquivalenceOfIso (eqToIso (congrArg (intervalMappingSpace x)
      (loopConeFixedApexComparison_endpoint t)))).isQCatEquivalence

/-- 既存の実 diagram fiber 比較は、厳密同型の下で同じ極限錐比較に一致する。 -/
lemma loopConeFixedApexDiagramFiberMap_interval {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    (loopConeFixedApexDiagramFiberIso t x).hom ≫
      loopConeClassifierDiagramFiberMap X x t.diagramVertex ≫
        (SerrePositivity.InfinityCategories.F1B.unitCommaFiberIntervalIso (loopDiagramEvaluation X 0 0) x t.diagramVertex).hom =
      loopConeFixedApexIntervalFamily t x := by
  apply intervalFamilyHomotopy_h_injective
  rw [intervalFamilyHomotopy_precomp_h, loopConeClassifierDiagramFiberMap_interval_h,
    loopConeFixedApexIntervalFamily, intervalFamilyHomotopy_eqToIso_target,
    terminalComparisonIntervalFamily_h]
  · rw [← Category.assoc, ← comp_whiskerRight, loopConeFixedApexDiagramFiberIso_lift]
    conv_rhs =>
      arg 2
      rw [coneFamilyApex_eq_vertexEvaluation]
    rw [← Category.assoc, loopConeFixedApexComparison_ι]
    simp only [loopConeApexComparisonHomotopy, Category.assoc]
  · exact loopConeFixedApexComparison_endpoint t

/-- 指定された実 loop 四角形上の、既存の図式 fiber 比較そのものは同値。 -/
lemma loopConeClassifierDiagramFiberMap_isQCatEquivalence_of_loopSquare
    {X : SSet.{u}} [Quasicategory X] {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    IsQCatEquivalence (loopConeClassifierDiagramFiberMap X x t.diagramVertex) := by
  have hW := (qCatEquivalenceOfIso (loopConeFixedApexDiagramFiberIso t x)).isQCatEquivalence
  have hI := (qCatEquivalenceOfIso (SerrePositivity.InfinityCategories.F1B.unitCommaFiberIntervalIso
    (loopDiagramEvaluation X 0 0) x t.diagramVertex)).isQCatEquivalence
  have h : IsQCatEquivalence ((loopConeFixedApexDiagramFiberIso t x).hom ≫
      loopConeClassifierDiagramFiberMap X x t.diagramVertex ≫
        (SerrePositivity.InfinityCategories.F1B.unitCommaFiberIntervalIso (loopDiagramEvaluation X 0 0) x
          t.diagramVertex).hom) := by
    rw [loopConeFixedApexDiagramFiberMap_interval]
    exact loopConeFixedApexIntervalFamily_isQCatEquivalence t x
  exact hI.cancel_right (hW.cancel_left h)

/-- 任意の実 loop 図式上で、既存の図式 fiber 比較そのものは同値。 -/
lemma loopConeClassifierDiagramFiberMap_isQCatEquivalence (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) (d : (loopDiagrams X) _⦋0⦌) :
    IsQCatEquivalence (loopConeClassifierDiagramFiberMap X x d) := by
  have h := loopConeClassifierDiagramFiberMap_isQCatEquivalence_of_loopSquare
    (loopSquareOfDiagramVertex d) x
  exact Eq.mp (congrArg (fun v ↦ IsQCatEquivalence (loopConeClassifierDiagramFiberMap X x v))
    (loopSquareOfDiagramVertex_diagramVertex d)) h

/-- 元の始点固定 loop 錐から comma への同じ実比較は同値。 -/
lemma loopConeClassifierSourceFiberMap_isQCatEquivalence (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) : IsQCatEquivalence (loopConeClassifierSourceFiberMap X x) :=
  loopConeClassifierSourceFiberMap_isQCatEquivalence_of_diagramFibers X x
    (loopConeClassifierDiagramFiberMap_isQCatEquivalence X x)
end SerrePositivity.InfinityCategories

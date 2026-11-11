module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeUniversalSelfComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeClassifierFiberEquivalence

/-!
概要：元の普遍 loop 錐の指定点の始対象性と、同じ零隅四角形への移送。
方針：固定 cospan の終対象の自己比較と、実 classifier・選択忘却を接続する。
規約：最後の全四角形図式を厳密に保つ。使われ方：同じ loop 四角形の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
def loopConeFixedApexSourceLift {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) x ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexDiagramFiberIso t x).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) t.diagramVertex

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeFixedApexSourceLift_ι {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    loopConeFixedApexSourceLift t x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexLift t x := by
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexDiagramFiberIso_lift t x

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeFixedApexSourceLift_classifier_h {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy
      (loopConeFixedApexSourceLift t x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x)).h =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexLift t x ▷ (Δ[1] : SSet.{u})) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeApexComparisonHomotopy X).h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy
    ((loopConeFixedApexSourceLift t x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) x)).h = _
  have hi : (loopConeFixedApexSourceLift t x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) x =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexLift t x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifier X := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap_ι, ← Category.assoc,
      loopConeFixedApexSourceLift_ι]
  exact (congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) x ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy q).h) hi).trans (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifier, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_lift_h])
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

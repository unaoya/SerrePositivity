module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeFixedApexComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FixedApexConeFiber
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberIntervalIso
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaHomotopySquare

/-!
概要：元の comma fiber 比較の区間族を、同じ実 loop 比較の円柱へ同定する。
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

/-- 区間の終点の等式輸送は、元の全パラメータの円柱を変えない。 -/
lemma intervalFamilyHomotopy_eqToIso_target {A X : SSet.{u}} {x y y' : X _⦋0⦌}
    (h : y = y') (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (f ≫ (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x) h)).hom)).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h := by
  cases h
  simp

/-- 極限錐の比較の終点は、元の loop 図式の始点評価に一致する。 -/
lemma loopConeFixedApexComparison_endpoint {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square)) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌) t.diagramVertex := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap_apex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square))
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square).vertex at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSquare_pullbackCone_vertex] at h
  refine h.trans ?_
  change t.vertex = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  rfl

/-- 既存の実 diagram fiber 比較の区間族は、同じ loop 比較の円柱を回収する。 -/
lemma loopConeClassifierDiagramFiberMap_interval_h (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) (d : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x d ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberIntervalIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x d).hom)).h =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) d ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x) ▷ (Δ[1] : SSet.{u})) ≫
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeApexComparisonHomotopy X).h := by
  have hi : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x d ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x) d ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) d ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifier X := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap_ι, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap_ι, ← Category.assoc]
  have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x d ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberIntervalIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x d).hom)).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x d ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x) d ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) x)).h := by
    change (β_ _ (Δ[1] : SSet.{u})).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierDiagramFiberMap X x d ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberToInterval (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x d) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberToInterval_uncurry,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry_precomp]
    rfl
  rw [hh, hi, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifier, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_lift_h]
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

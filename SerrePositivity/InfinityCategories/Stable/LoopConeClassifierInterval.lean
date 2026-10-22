module
public import SerrePositivity.InfinityCategories.Stable.LoopConeFixedApexComparison
public import SerrePositivity.InfinityCategories.Stable.FixedApexConeFiber
public import SerrePositivity.InfinityCategories.F1B.KanUnitCommaFiberIntervalIso
public import SerrePositivity.InfinityCategories.F1B.UnitCommaHomotopySquare

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
namespace SerrePositivity.InfinityCategories

/-- 区間の終点の等式輸送は、元の全パラメータの円柱を変えない。 -/
lemma intervalFamilyHomotopy_eqToIso_target {A X : SSet.{u}} {x y y' : X _⦋0⦌}
    (h : y = y') (f : A ⟶ intervalMappingSpace x y) :
    (intervalFamilyHomotopy (f ≫ (eqToIso (congrArg (intervalMappingSpace x) h)).hom)).h =
      (intervalFamilyHomotopy f).h := by
  cases h
  simp

/-- 極限錐の比較の終点は、元の loop 図式の始点評価に一致する。 -/
lemma loopConeFixedApexComparison_endpoint {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) :
    (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)).app (Opposite.op ⦋0⦌)
      ((sliceConeFamilyMap (pullbackCospan t.square)).app (Opposite.op ⦋0⦌)
        (pullbackCone t.square)) =
      (loopDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌) t.diagramVertex := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (pullbackCone t.square))
    (HomotopyLimits.sliceConeFamilyMap_apex (pullbackCospan t.square))
  change _ = (pullbackCone t.square).vertex at h
  rw [loopSquare_pullbackCone_vertex] at h
  refine h.trans ?_
  change t.vertex = (evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
      (Opposite.op ⦋0⦌) (functorVertex t.square)
  rw [evaluateFunctorAt_functorVertex]
  rfl

/-- 既存の実 diagram fiber 比較の区間族は、同じ loop 比較の円柱を回収する。 -/
lemma loopConeClassifierDiagramFiberMap_interval_h (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) (d : (loopDiagrams X) _⦋0⦌) :
    (intervalFamilyHomotopy (loopConeClassifierDiagramFiberMap X x d ≫
      (F1B.kanUnitCommaFiberIntervalIso (loopDiagramEvaluation X 0 0) x d).hom)).h =
      ((vertexFiberι (loopConeSourceFiberProjection X x) d ≫
        vertexFiberι (loopConeObjectSource X) x) ▷ (Δ[1] : SSet.{u})) ≫
          (loopConeApexComparisonHomotopy X).h := by
  have hi : loopConeClassifierDiagramFiberMap X x d ≫
      vertexFiberι (F1B.kanUnitCommaFiberProjection (loopDiagramEvaluation X 0 0) x) d ≫
        vertexFiberι (unitCommaSource (loopDiagramEvaluation X 0 0)) x =
      (vertexFiberι (loopConeSourceFiberProjection X x) d ≫
        vertexFiberι (loopConeObjectSource X) x) ≫ loopConeClassifier X := by
    rw [← Category.assoc, loopConeClassifierDiagramFiberMap_ι, Category.assoc,
      loopConeClassifierSourceFiberMap_ι, ← Category.assoc]
  have hh : (intervalFamilyHomotopy (loopConeClassifierDiagramFiberMap X x d ≫
        (F1B.kanUnitCommaFiberIntervalIso (loopDiagramEvaluation X 0 0) x d).hom)).h =
      (unitCommaHomotopy (loopConeClassifierDiagramFiberMap X x d ≫
        vertexFiberι (F1B.kanUnitCommaFiberProjection (loopDiagramEvaluation X 0 0) x) d ≫
          vertexFiberι (unitCommaSource (loopDiagramEvaluation X 0 0)) x)).h := by
    change (β_ _ (Δ[1] : SSet.{u})).hom ≫
      intervalMappingUncurry (loopConeClassifierDiagramFiberMap X x d ≫
        F1B.kanUnitCommaFiberToInterval (loopDiagramEvaluation X 0 0) x d) = _
    rw [intervalMappingUncurry_precomp, F1B.kanUnitCommaFiberToInterval_uncurry,
      ← unitCommaUncurry_precomp]
    rfl
  rw [hh, hi, unitCommaHomotopy_precomp, loopConeClassifier, unitCommaHomotopy_lift_h]
end SerrePositivity.InfinityCategories

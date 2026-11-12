module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationChartLegs
/-!
概要：元の coherent bar 評価余錐は、filtered 空間判定の五条件を満たす。
方針：同じホモロジー余錐の普遍性と、実 transition・脚の自然な全基点チャートを使う。
規約：全 native coherent 図式を扱い、strict 性や compact 性を追加仮定にしない。
使われ方：Ind-π の橋への無条件の実入力と c2。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I] [IsFiltered I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D)
  (x : D)

/-- 同じ任意の実余錐のホモロジー余極限性から五条件のチャートを作る。 -/
def dgBarCompactEvaluationHomologyCharts (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G)
    (hc : ∀ n : ℕ, IsColimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCoefficientCocone R D G c x n)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactHomologyCharts R
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceStage (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceApex (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCocone R D G c x))
      (fun {_ _} h => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceTransition (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x) h)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceLeg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCocone R D G c x)) where
  diagram := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCoefficientDiagram R D G x
  cocone := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCoefficientCocone R D G c x
  isColimit := hc
  zeroStage := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiZeroChart R D G x
  zeroApex := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationApexPiZeroChart R D G c x
  zero_leg i y := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiZeroChart_leg R D G c x i).app (SSet.π₀.mk y)
  zero_transition h y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiZeroChart_naturality R D G x h (SSet.π₀.mk y)
  positiveStage n i := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiChart R D G x n i).equiv
  positiveApex n := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationApexPiChart R D G c x n).equiv
  positive_leg n i y a := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiChart_leg R D G c x n i).app y a
  positive_transition n {_ _} h y a := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiChart_naturality R D G x h n).app y a
  transport n {_ _} e a b h := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart.transport_iff
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationApexPiChart R D G c x n) e a b).mpr h

/-- 同じ実 bar 評価余錐の全次数ホモロジーチャート。 -/
def dgBarCompactNativeEvaluationHomologyCharts :=
  dgBarCompactEvaluationHomologyCharts R D G x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone R D G)
    (fun n => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveHomologyCocone_isColimit R D G x (-(n : ℤ)))

/-- 全 native coherent 図式について、同じ bar 評価余錐が五条件を満たす。 -/
lemma dgBarCompactNativeEvaluationPiData :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactFilteredSpacePiData (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetCocone R D G x) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiData_of_homologyCharts (dgBarCompactNativeEvaluationHomologyCharts R D G x)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

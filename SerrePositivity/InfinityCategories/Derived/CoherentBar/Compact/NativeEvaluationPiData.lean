module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationChartLegs
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I] [IsFiltered I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ dgProjectiveModuleNerve R D)
  (x : D)

/-- 同じ任意の実余錐のホモロジー余極限性から五条件のチャートを作る。 -/
def dgBarCompactEvaluationHomologyCharts (c : JoinCocone G)
    (hc : ∀ n : ℕ, IsColimit (dgBarCompactEvaluationCoefficientCocone R D G c x n)) :
    DGBarCompactHomologyCharts R
      (dgBarCompactSpaceStage (dgBarCompactEvaluationPosetDiagram R D G x))
      (dgBarCompactSpaceApex (dgBarCompactEvaluationPosetDiagram R D G x)
        (dgBarCompactEvaluationCocone R D G c x))
      (fun {_ _} h => dgBarCompactSpaceTransition (dgBarCompactEvaluationPosetDiagram R D G x) h)
      (dgBarCompactSpaceLeg (dgBarCompactEvaluationPosetDiagram R D G x)
        (dgBarCompactEvaluationCocone R D G c x)) where
  diagram := dgBarCompactEvaluationCoefficientDiagram R D G x
  cocone := dgBarCompactEvaluationCoefficientCocone R D G c x
  isColimit := hc
  zeroStage := dgBarCompactEvaluationStagePiZeroChart R D G x
  zeroApex := dgBarCompactEvaluationApexPiZeroChart R D G c x
  zero_leg i y := (dgBarCompactEvaluationPiZeroChart_leg R D G c x i).app (SSet.π₀.mk y)
  zero_transition h y := dgBarCompactEvaluationStagePiZeroChart_naturality R D G x h (SSet.π₀.mk y)
  positiveStage n i := (dgBarCompactEvaluationStagePiChart R D G x n i).equiv
  positiveApex n := (dgBarCompactEvaluationApexPiChart R D G c x n).equiv
  positive_leg n i y a := (dgBarCompactEvaluationPiChart_leg R D G c x n i).app y a
  positive_transition n {_ _} h y a := (dgBarCompactEvaluationStagePiChart_naturality R D G x h n).app y a
  transport n {_ _} e a b h := (DGBarCompactPiChart.transport_iff
    (dgBarCompactEvaluationApexPiChart R D G c x n) e a b).mpr h

/-- 同じ実 bar 評価余錐の全次数ホモロジーチャート。 -/
def dgBarCompactNativeEvaluationHomologyCharts :=
  dgBarCompactEvaluationHomologyCharts R D G x (dgProjectiveBarNativeCocone R D G)
    (fun n => dgBarCompactProjectiveHomologyCocone_isColimit R D G x (-(n : ℤ)))

/-- 全 native coherent 図式について、同じ bar 評価余錐が五条件を満たす。 -/
lemma dgBarCompactNativeEvaluationPiData :
    DGBarCompactFilteredSpacePiData (dgBarCompactEvaluationPosetDiagram R D G x)
      (dgBarCompactEvaluationPosetCocone R D G x) :=
  dgBarCompactPiData_of_homologyCharts (dgBarCompactNativeEvaluationHomologyCharts R D G x)

end SerrePositivity.InfinityCategories

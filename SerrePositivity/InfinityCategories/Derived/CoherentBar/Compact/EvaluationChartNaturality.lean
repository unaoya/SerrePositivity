module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationHomologyCharts
/-!
概要：元の bar 評価チャートは、同じホモロジー図式の transition と可換する。
方針：実辺の全基点自然性と H⁰ 図式の対象同型の逆自然性を合成する。
規約：元の native 辺を保持する。
使われ方：ホモロジー余錐から filtered 空間の五条件への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ dgProjectiveModuleNerve R D)
  (c : JoinCocone G) (x : D)

lemma dgBarCompactEvaluationStagePiChart_naturality {i j : I} (h : i ≤ j) (n : ℕ) :
    DGBarCompactPiChartNaturality
      (dgBarCompactEvaluationStagePiChart R D G x n i)
      (dgBarCompactEvaluationStagePiChart R D G x n j)
      (dgBarCompactSpaceTransition (dgBarCompactEvaluationPosetDiagram R D G x) h)
      ((dgBarCompactEvaluationCoefficientDiagram R D G x (n + 1)).map (homOfLE h)).hom := by
  constructor
  intro y a
  rw [dgBarCompactEvaluationTransition_eq]
  have hn := (dgBarCompactEvaluationVertexPiChart_naturality R D x
    (dgBarCompactEvaluationIndexEdge R D G h) n).app y a
  rw [dgBarCompactEvaluationTransitionClosed_eq] at hn
  have hc := ConcreteCategory.congr_hom
    (dgBarCompactEvaluationStageHomologyIso_inv_naturality R D G x
      (-((n + 1 : ℕ) : ℤ)) (homOfLE h))
    ((dgBarCompactEvaluationVertexPiChart R D x
      (dgBarCompactEvaluationStageVertex R D G i) n).equiv y a)
  dsimp only [dgBarCompactEvaluationStagePiChart, DGBarCompactPiChart.postcompose,
    Equiv.trans_apply]
  exact (congrArg (fun b => (dgBarCompactEvaluationStageHomologyIso R D G x
    (-((n + 1 : ℕ) : ℤ)) j).inv b) hn).trans hc

lemma dgBarCompactEvaluationStagePiZeroChart_naturality {i j : I} (h : i ≤ j) (a) :
    dgBarCompactEvaluationStagePiZeroChart R D G x j
      (SSet.mapπ₀ (dgBarCompactSpaceTransition (dgBarCompactEvaluationPosetDiagram R D G x) h) a) =
      (dgBarCompactEvaluationCoefficientDiagram R D G x 0).map (homOfLE h)
        (dgBarCompactEvaluationStagePiZeroChart R D G x i a) := by
  rw [dgBarCompactEvaluationTransition_eq]
  have hn := dgBarCompactEvaluationVertexPiZeroChart_naturality R D x
    (dgBarCompactEvaluationIndexEdge R D G h) a
  rw [dgBarCompactEvaluationTransitionClosed_eq] at hn
  have hc := ConcreteCategory.congr_hom
    (dgBarCompactEvaluationStageHomologyIso_inv_naturality R D G x 0 (homOfLE h))
    (dgBarCompactEvaluationVertexPiZeroChart R D x
      (dgBarCompactEvaluationStageVertex R D G i) a)
  exact (congrArg (fun b => (dgBarCompactEvaluationStageHomologyIso R D G x 0 j).inv b) hn).trans hc

end SerrePositivity.InfinityCategories

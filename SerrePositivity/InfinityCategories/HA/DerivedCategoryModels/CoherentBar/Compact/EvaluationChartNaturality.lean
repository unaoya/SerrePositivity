module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationHomologyCharts
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits DifferentialGraded SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (x : D)

lemma dgBarCompactEvaluationStagePiChart_naturality {i j : I} (h : i ≤ j) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChartNaturality
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiChart R D G x n i)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiChart R D G x n j)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceTransition (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x) h)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCoefficientDiagram R D G x (n + 1)).map (homOfLE h)).hom := by
  constructor
  intro y a
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationTransition_eq]
  have hn := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiChart_naturality R D x
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationIndexEdge R D G h) n).app y a
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationTransitionClosed_eq] at hn
  have hc := ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageHomologyIso_inv_naturality R D G x
      (-((n + 1 : ℕ) : ℤ)) (homOfLE h))
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiChart R D x
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageVertex R D G i) n).equiv y a)
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiChart, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart.postcompose,
    Equiv.trans_apply]
  exact (congrArg (fun b => (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageHomologyIso R D G x
    (-((n + 1 : ℕ) : ℤ)) j).inv b) hn).trans hc

lemma dgBarCompactEvaluationStagePiZeroChart_naturality {i j : I} (h : i ≤ j) (a) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiZeroChart R D G x j
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceTransition (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x) h) a) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCoefficientDiagram R D G x 0).map (homOfLE h)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiZeroChart R D G x i a) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationTransition_eq]
  have hn := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiZeroChart_naturality R D x
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationIndexEdge R D G h) a
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationTransitionClosed_eq] at hn
  have hc := ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageHomologyIso_inv_naturality R D G x 0 (homOfLE h))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiZeroChart R D x
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageVertex R D G i) a)
  exact (congrArg (fun b => (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageHomologyIso R D G x 0 j).inv b) hn).trans hc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

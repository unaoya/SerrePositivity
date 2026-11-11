module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationChartNaturality
/-!
概要：元の評価チャートは、同じ bar ホモロジー余錐の全ての脚と可換する。
方針：元の実脚の自然性を同じ頂点表示へ運び、H⁰ 対象同型を相殺する。
規約：元の実 bar 余錐そのものを使う。
使われ方：filtered 空間の五条件と c2 の無条件化。
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

lemma dgBarCompactEvaluationPiChart_leg (n : ℕ) (i : I) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChartNaturality
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiChart R D G x n i)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationApexPiChart R D G c x n)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceLeg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCocone R D G c x) i)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCoefficientCocone R D G c x (n + 1)).ι.app i).hom := by
  have hn := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiChart_naturality R D x
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationLegEdge R D G c i) n).cast rfl
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationApexSpace_eq R D G c x)
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationLeg_eq] at hn
  exact hn.reparam_source
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageHomologyIso R D G x (-((n + 1 : ℕ) : ℤ)) i).symm.toLinearEquiv.toEquiv
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCoefficientCocone R D G c x (n + 1)).ι.app i).hom
    (fun a => (ConcreteCategory.congr_hom
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationHomologyLeg R D G c x (-((n + 1 : ℕ) : ℤ)) i) a).symm)

set_option maxHeartbeats 1000000 in
lemma dgBarCompactEvaluationPiZeroChart_leg (i : I) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiZeroChartNaturality
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStagePiZeroChart R D G x i)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationApexPiZeroChart R D G c x)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceLeg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCocone R D G c x) i)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCoefficientCocone R D G c x 0).ι.app i).hom := by
  have hr : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiZeroChartNaturality
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiZeroChart R D x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageVertex R D G i))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiZeroChart R D x c.vertex)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationEdgeValue R D x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationLegEdge R D G c i)) _ :=
    ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiZeroChart_naturality R D x
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationLegEdge R D G c i)⟩
  have hn := hr.cast rfl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationApexSpace_eq R D G c x)
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationLeg_eq] at hn
  exact hn.reparam_source
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageHomologyIso R D G x 0 i).symm.toLinearEquiv.toEquiv
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationCoefficientCocone R D G c x 0).ι.app i).hom
    (fun a => (ConcreteCategory.congr_hom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationHomologyLeg R D G c x 0 i) a).symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

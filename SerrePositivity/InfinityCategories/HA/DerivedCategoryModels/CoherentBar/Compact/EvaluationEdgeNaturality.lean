module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationClosedNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationVertexPiChart
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveH0Naturality
/-!
概要：元の任意の native 辺に沿う全基点評価チャートの自然性。
方針：同じ辺の閉射を回収し、頂点再構成の等式を同時に輸送する。
規約：図式の辺と余錐の脚を strict 図式へ置換しない。
使われ方：coherent bar の実評価余錐をホモロジー余錐と照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarCompactEvaluationRecoveredClosedEdge
    {y z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D).Edge y z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated)).edge = e.edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (x := y) (y := z)
    (closedHomEquiv R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated))).edge = e.edge
  have hc := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle e.toTruncated
  change closedHomEquiv R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) (y.obj 0) (z.obj 0)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle e.toTruncated at hc
  rw [hc]
  exact congrArg SSet.Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle_edgeCycle e.toTruncated)

def dgBarCompactEvaluationEdgeValue (x : D)
    {y z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D).Edge y z) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue
    ((SSet.Edge.ofTruncated
      (X := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1} e.toTruncated)).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x))

lemma dgBarCompactEvaluationEdgeCast_eq (x : D)
    {y z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D).Edge y z) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceMapCast (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexSpace_eq R D x y)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexSpace_eq R D x z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationClosedEdgeValue R D x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated)) =
        dgBarCompactEvaluationEdgeValue R D x e := by
  apply eq_of_heq
  apply (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceMapCast_heq _ _ _).trans
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceEdgeValue_heq
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated)).edge) = _
  rw [dgBarCompactEvaluationRecoveredClosedEdge]
  rfl

lemma dgBarCompactEvaluationVertexPiChart_naturality (x : D)
    {y z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D).Edge y z) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChartNaturality
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiChart R D x y n)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiChart R D x z n) (dgBarCompactEvaluationEdgeValue R D x e)
      (HomologicalComplex.homologyMap ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
        (e.toTruncated.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)))))))
        (-((n + 1 : ℕ) : ℤ))).hom := by
  have h := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiChart_closedNaturality R D x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated) n).cast
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexSpace_eq R D x y) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexSpace_eq R D x z)
  change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChartNaturality
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiChart R D x y n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiChart R D x z n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceMapCast (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexSpace_eq R D x y)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexSpace_eq R D x z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationClosedEdgeValue R D x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated))) _ at h
  rw [dgBarCompactEvaluationEdgeCast_eq, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveEdgeClosed_map] at h
  exact h

lemma dgBarCompactEvaluationVertexPiZeroChart_naturality (x : D)
    {y z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D).Edge y z) (a) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiZeroChart R D x z
      (SSet.mapπ₀ (dgBarCompactEvaluationEdgeValue R D x e) a) =
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
        (e.toTruncated.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D))))))) 0
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexPiZeroChart R D x y a) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiZeroChart_cast_naturality
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexSpace_eq R D x y) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationVertexSpace_eq R D x z)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiZeroChart R D x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv y))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiZeroChart R D x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv z))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationClosedEdgeValue R D x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated)) _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiZeroChart_closedNaturality R D x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated)) a
  rw [dgBarCompactEvaluationEdgeCast_eq, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveEdgeClosed_map] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

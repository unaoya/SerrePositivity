module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModuleValueEdgeEquality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationScalarClosedMap
/-!
概要：射影的加群の実閉辺に沿う評価チャートの自然性。
方針：同じ dg 評価射の加群値チャートを元の native 閉辺へ厳密に照合する。
規約：頂点表示と実辺を同時に輸送する。
使われ方：coherent bar の元の transition と余錐の脚への適用。
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

/-- 元の射影的加群の閉辺を、実評価空間関手で写した作用。 -/
def dgBarCompactEvaluationClosedEdgeValue (x : D)
    {M N : ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)} (f : M ⟶ N) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue
    ((SSet.Edge.ofTruncated
      (X := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) f))).map
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x))

/-- 同じ加群評価作用を元の実頂点表示へ輸送する。 -/
def dgBarCompactEvaluationClosedEdgeCast (x : D)
    {M N : ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)} (f : M ⟶ N) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)))).obj ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)))).obj :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceMapCast (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationValueSpace_eq R D x M)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationValueSpace_eq R D x N)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValueEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationModuleDG R D x).onClosed.map f))

lemma dgBarCompactEvaluationClosedEdgeCast_eq (x : D)
    {M N : ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)} (f : M ⟶ N) :
    dgBarCompactEvaluationClosedEdgeCast R D x f =
      dgBarCompactEvaluationClosedEdgeValue R D x f := by
  let E := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationModuleDG R D x
  let Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})
  have hf : (E.comp Q).onClosed.map f = Q.onClosed.map (E.onClosed.map f) := by
    have h := (EnrichedFunctor.forgetComp E Q).hom.naturality f
    change (E.comp Q).onClosed.map f ≫ 𝟙 _ = 𝟙 _ ≫ Q.onClosed.map (E.onClosed.map f) at h
    simpa only [Category.comp_id, Category.id_comp] using h
  have hraw : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValueNativeEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
      (E.onClosed.map f)) (dgBarCompactEvaluationClosedEdgeValue R D x f) := by
    apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceEdgeValue_heq
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)).app (Opposite.op ⦋1⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
        (Q.onClosed.map (E.onClosed.map f))).edge) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)).app (Opposite.op ⦋1⦌)
        (ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) f).edge.map (E.comp Q)))
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map, hf]
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceMapCast_heq _ _ _).trans
    ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValueEdge_eq_native R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
      (E.onClosed.map f))).trans hraw))

lemma dgBarCompactEvaluationPiChart_closedNaturality (x : D)
    {M N : ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)} (f : M ⟶ N) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChartNaturality
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiChart R D x M n) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiChart R D x N n)
      (dgBarCompactEvaluationClosedEdgeValue R D x f)
      (HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        ((_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).onClosed.map f)) (-((n + 1 : ℕ) : ℤ))).hom := by
  have h := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValuePiChart_naturality R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationModuleDG R D x).onClosed.map f) n).cast
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationValueSpace_eq R D x M) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationValueSpace_eq R D x N)
  change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChartNaturality
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiChart R D x M n) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiChart R D x N n)
    (dgBarCompactEvaluationClosedEdgeCast R D x f) _ at h
  rw [dgBarCompactEvaluationClosedEdgeCast_eq, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationScalarClosedMap] at h
  exact h

lemma dgBarCompactEvaluationPiZeroChart_closedNaturality (x : D)
    {M N : ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)} (f : M ⟶ N) (a) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiZeroChart R D x N
      (SSet.mapπ₀ (dgBarCompactEvaluationClosedEdgeValue R D x f) a) =
      HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        ((_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).onClosed.map f)) 0
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiZeroChart R D x M a) := by
  rw [← dgBarCompactEvaluationClosedEdgeCast_eq]
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiZeroChart_cast_naturality
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationValueSpace_eq R D x M) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationValueSpace_eq R D x N)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValuePiZeroChart R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationModuleDG R D x).obj M))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValuePiZeroChart R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationModuleDG R D x).obj N))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValueEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationModuleDG R D x).onClosed.map f)) _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValuePiZeroChart_naturality R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationModuleDG R D x).onClosed.map f)) a
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationScalarClosedMap] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

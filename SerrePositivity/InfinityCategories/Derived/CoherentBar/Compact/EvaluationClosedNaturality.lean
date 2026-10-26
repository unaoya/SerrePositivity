module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleValueEdgeEquality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationScalarClosedMap
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の射影的加群の閉辺を、実評価空間関手で写した作用。 -/
def dgBarCompactEvaluationClosedEdgeValue (x : D)
    {M N : ClosedCategory R (ProjectiveDGModules R D)} (f : M ⟶ N) :=
  F2.spaceInfinityEdgeValue
    ((SSet.Edge.ofTruncated
      (X := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (dgProjectiveModuleNerve R D))
      (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (dgClosedEdge R (ProjectiveDGModules R D) f))).map
          (dgBarCompactProjectiveEvaluationSpaceInfinity R D x))

/-- 同じ加群評価作用を元の実頂点表示へ輸送する。 -/
def dgBarCompactEvaluationClosedEdgeCast (x : D)
    {M N : ClosedCategory R (ProjectiveDGModules R D)} (f : M ⟶ N) :
    (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex M)))).obj ⟶
    (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex N)))).obj :=
  dgBarCompactSpaceMapCast (dgBarCompactEvaluationValueSpace_eq R D x M)
    (dgBarCompactEvaluationValueSpace_eq R D x N)
    (dgBarCompactModuleValueEdge R (ProjectiveDGModules R D)
      ((dgBarCompactProjectiveEvaluationModuleDG R D x).onClosed.map f))

lemma dgBarCompactEvaluationClosedEdgeCast_eq (x : D)
    {M N : ClosedCategory R (ProjectiveDGModules R D)} (f : M ⟶ N) :
    dgBarCompactEvaluationClosedEdgeCast R D x f =
      dgBarCompactEvaluationClosedEdgeValue R D x f := by
  let E := dgBarCompactProjectiveEvaluationModuleDG R D x
  let Q := dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})
  have hf : (E.comp Q).onClosed.map f = Q.onClosed.map (E.onClosed.map f) := by
    have h := (EnrichedFunctor.forgetComp E Q).hom.naturality f
    change (E.comp Q).onClosed.map f ≫ 𝟙 _ = 𝟙 _ ≫ Q.onClosed.map (E.onClosed.map f) at h
    simpa only [Category.comp_id, Category.id_comp] using h
  have hraw : HEq (dgBarCompactModuleValueNativeEdge R (ProjectiveDGModules R D)
      (E.onClosed.map f)) (dgBarCompactEvaluationClosedEdgeValue R D x f) := by
    apply dgBarCompactSpaceEdgeValue_heq
    change (dgHomUnderlyingSpaceInfinity R (ProjectiveDGModules R D)).app (Opposite.op ⦋1⦌)
      (ULift.up (dgClosedEdge R
        (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
        (Q.onClosed.map (E.onClosed.map f))).edge) =
      (dgHomUnderlyingSpaceInfinity R (ProjectiveDGModules R D)).app (Opposite.op ⦋1⦌)
        (ULift.up ((dgClosedEdge R (ProjectiveDGModules R D) f).edge.map (E.comp Q)))
    rw [dgClosedEdge_map, hf]
  exact eq_of_heq ((dgBarCompactSpaceMapCast_heq _ _ _).trans
    ((heq_of_eq (dgBarCompactModuleValueEdge_eq_native R (ProjectiveDGModules R D)
      (E.onClosed.map f))).trans hraw))

lemma dgBarCompactEvaluationPiChart_closedNaturality (x : D)
    {M N : ClosedCategory R (ProjectiveDGModules R D)} (f : M ⟶ N) (n : ℕ) :
    DGBarCompactPiChartNaturality
      (dgBarCompactEvaluationPiChart R D x M n) (dgBarCompactEvaluationPiChart R D x N n)
      (dgBarCompactEvaluationClosedEdgeValue R D x f)
      (HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
        ((dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleProjectiveProperty R D)).onClosed.map f)) (-((n + 1 : ℕ) : ℤ))).hom := by
  have h := (dgBarCompactModuleValuePiChart_naturality R (ProjectiveDGModules R D)
    ((dgBarCompactProjectiveEvaluationModuleDG R D x).onClosed.map f) n).cast
      (dgBarCompactEvaluationValueSpace_eq R D x M) (dgBarCompactEvaluationValueSpace_eq R D x N)
  change DGBarCompactPiChartNaturality
    (dgBarCompactEvaluationPiChart R D x M n) (dgBarCompactEvaluationPiChart R D x N n)
    (dgBarCompactEvaluationClosedEdgeCast R D x f) _ at h
  rw [dgBarCompactEvaluationClosedEdgeCast_eq, dgBarCompactEvaluationScalarClosedMap] at h
  exact h

lemma dgBarCompactEvaluationPiZeroChart_closedNaturality (x : D)
    {M N : ClosedCategory R (ProjectiveDGModules R D)} (f : M ⟶ N) (a) :
    dgBarCompactEvaluationPiZeroChart R D x N
      (SSet.mapπ₀ (dgBarCompactEvaluationClosedEdgeValue R D x f) a) =
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
        ((dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleProjectiveProperty R D)).onClosed.map f)) 0
        (dgBarCompactEvaluationPiZeroChart R D x M a) := by
  rw [← dgBarCompactEvaluationClosedEdgeCast_eq]
  have h := dgBarCompactPiZeroChart_cast_naturality
    (dgBarCompactEvaluationValueSpace_eq R D x M) (dgBarCompactEvaluationValueSpace_eq R D x N)
    (dgBarCompactModuleValuePiZeroChart R (ProjectiveDGModules R D)
      ((dgBarCompactProjectiveEvaluationModuleDG R D x).obj M))
    (dgBarCompactModuleValuePiZeroChart R (ProjectiveDGModules R D)
      ((dgBarCompactProjectiveEvaluationModuleDG R D x).obj N))
    (dgBarCompactModuleValueEdge R (ProjectiveDGModules R D)
      ((dgBarCompactProjectiveEvaluationModuleDG R D x).onClosed.map f)) _
    (dgBarCompactModuleValuePiZeroChart_naturality R (ProjectiveDGModules R D)
      ((dgBarCompactProjectiveEvaluationModuleDG R D x).onClosed.map f)) a
  rw [dgBarCompactEvaluationScalarClosedMap] at h
  exact h

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationClosedNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationVertexPiChart
public import SerrePositivity.InfinityCategories.Derived.DGNerveH0Naturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarCompactEvaluationRecoveredClosedEdge
    {y z : (dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (dgProjectiveModuleNerve R D).Edge y z) :
    (dgClosedEdge R (ProjectiveDGModules R D) (edgeClosed e.toTruncated)).edge = e.edge := by
  change (edgeOfCycle (x := y) (y := z)
    (closedHomEquiv R (ProjectiveDGModules R D) _ _ (edgeClosed e.toTruncated))).edge = e.edge
  have hc := edgeClosed_cycle e.toTruncated
  change closedHomEquiv R (ProjectiveDGModules R D) (y.obj 0) (z.obj 0)
    (edgeClosed e.toTruncated) = edgeCycle e.toTruncated at hc
  rw [hc]
  exact congrArg SSet.Truncated.Edge.edge (edgeOfCycle_edgeCycle e.toTruncated)

def dgBarCompactEvaluationEdgeValue (x : D)
    {y z : (dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (dgProjectiveModuleNerve R D).Edge y z) :=
  F2.spaceInfinityEdgeValue
    ((SSet.Edge.ofTruncated
      (X := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (dgProjectiveModuleNerve R D))
      (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1} e.toTruncated)).map
        (dgBarCompactProjectiveEvaluationSpaceInfinity R D x))

lemma dgBarCompactEvaluationEdgeCast_eq (x : D)
    {y z : (dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (dgProjectiveModuleNerve R D).Edge y z) :
    dgBarCompactSpaceMapCast (dgBarCompactEvaluationVertexSpace_eq R D x y)
      (dgBarCompactEvaluationVertexSpace_eq R D x z)
      (dgBarCompactEvaluationClosedEdgeValue R D x (edgeClosed e.toTruncated)) =
        dgBarCompactEvaluationEdgeValue R D x e := by
  apply eq_of_heq
  apply (dgBarCompactSpaceMapCast_heq _ _ _).trans
  apply dgBarCompactSpaceEdgeValue_heq
  change (dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
    (ULift.up (dgClosedEdge R (ProjectiveDGModules R D) (edgeClosed e.toTruncated)).edge) = _
  rw [dgBarCompactEvaluationRecoveredClosedEdge]
  rfl

lemma dgBarCompactEvaluationVertexPiChart_naturality (x : D)
    {y z : (dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (dgProjectiveModuleNerve R D).Edge y z) (n : ℕ) :
    DGBarCompactPiChartNaturality
      (dgBarCompactEvaluationVertexPiChart R D x y n)
      (dgBarCompactEvaluationVertexPiChart R D x z n) (dgBarCompactEvaluationEdgeValue R D x e)
      (HomologicalComplex.homologyMap ((moduleEvaluation R D x).map (edgeClosed
        (e.toTruncated.map ((truncation 2).map (dgNerve.map
          (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)))))))
        (-((n + 1 : ℕ) : ℤ))).hom := by
  have h := (dgBarCompactEvaluationPiChart_closedNaturality R D x (edgeClosed e.toTruncated) n).cast
    (dgBarCompactEvaluationVertexSpace_eq R D x y) (dgBarCompactEvaluationVertexSpace_eq R D x z)
  change DGBarCompactPiChartNaturality
    (dgBarCompactEvaluationVertexPiChart R D x y n)
    (dgBarCompactEvaluationVertexPiChart R D x z n)
    (dgBarCompactSpaceMapCast (dgBarCompactEvaluationVertexSpace_eq R D x y)
      (dgBarCompactEvaluationVertexSpace_eq R D x z)
      (dgBarCompactEvaluationClosedEdgeValue R D x (edgeClosed e.toTruncated))) _ at h
  rw [dgBarCompactEvaluationEdgeCast_eq, ← dgNerveEdgeClosed_map] at h
  exact h

lemma dgBarCompactEvaluationVertexPiZeroChart_naturality (x : D)
    {y z : (dgProjectiveModuleNerve R D) _⦋0⦌}
    (e : (dgProjectiveModuleNerve R D).Edge y z) (a) :
    dgBarCompactEvaluationVertexPiZeroChart R D x z
      (SSet.mapπ₀ (dgBarCompactEvaluationEdgeValue R D x e) a) =
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map (edgeClosed
        (e.toTruncated.map ((truncation 2).map (dgNerve.map
          (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D))))))) 0
        (dgBarCompactEvaluationVertexPiZeroChart R D x y a) := by
  have h := dgBarCompactPiZeroChart_cast_naturality
    (dgBarCompactEvaluationVertexSpace_eq R D x y) (dgBarCompactEvaluationVertexSpace_eq R D x z)
    (dgBarCompactEvaluationPiZeroChart R D x (Simplex.vertexEquiv y))
    (dgBarCompactEvaluationPiZeroChart R D x (Simplex.vertexEquiv z))
    (dgBarCompactEvaluationClosedEdgeValue R D x (edgeClosed e.toTruncated)) _
    (dgBarCompactEvaluationPiZeroChart_closedNaturality R D x (edgeClosed e.toTruncated)) a
  rw [dgBarCompactEvaluationEdgeCast_eq, ← dgNerveEdgeClosed_map] at h
  exact h

end SerrePositivity.InfinityCategories

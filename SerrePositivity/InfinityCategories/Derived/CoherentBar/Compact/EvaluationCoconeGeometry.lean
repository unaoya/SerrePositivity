module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationEdgeNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.CoconeLegNaturality
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost
/-!
概要：元の bar 評価余錐の頂点・transition・脚を同じ native データで表示する。
方針：添字の宇宙比較と脚の三つの自然性を一単体上で照合する。
規約：元の実余錐と全ての実辺を維持する。
使われ方：ホモロジー余錐の普遍性を空間の五条件へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ dgProjectiveModuleNerve R D)
  (c : JoinCocone G) (x : D)

/-- 同じ任意の実余錐を、平坦化した添字上で評価する。 -/
def dgBarCompactEvaluationCocone : JoinCocone (dgBarCompactEvaluationPosetDiagram R D G x) :=
  (mapJoinCocone (dgBarCompactProjectiveEvaluationSpaceInfinity R D x)
    (JoinCocone.ulift c)).restrict (dgBarCompactIndexLiftIso.{u, v} (nerve I)).hom

abbrev dgBarCompactEvaluationStageVertex (i : I) :=
  G.app (Opposite.op ⦋0⦌) (ULift.up (nerveEquiv.symm i))

def dgBarCompactEvaluationIndexEdge {i j : I} (h : i ≤ j) :
    (dgProjectiveModuleNerve R D).Edge
      (dgBarCompactEvaluationStageVertex R D G i) (dgBarCompactEvaluationStageVertex R D G j) :=
  (SSet.Edge.ofTruncated
    (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I))
    (uliftTruncatedEdge.{u, max (u + 1) v} (CategoryTheory.nerve.edgeMk (homOfLE h)).toTruncated)).map G

lemma dgBarCompactEvaluationTransition_eq {i j : I} (h : i ≤ j) :
    dgBarCompactSpaceTransition (dgBarCompactEvaluationPosetDiagram R D G x) h =
      dgBarCompactEvaluationEdgeValue R D x (dgBarCompactEvaluationIndexEdge R D G h) := by
  apply eq_of_heq
  apply dgBarCompactSpaceEdgeValue_heq
  rfl

def dgBarCompactEvaluationLegEdge (i : I) :
    (dgProjectiveModuleNerve R D).Edge
      (dgBarCompactEvaluationStageVertex R D G i) c.vertex :=
  (simplicialHomotopyVertexEdge
    (F2.coconeTransformationHomotopy c)
      (ULift.up (nerveEquiv.symm i))).ofEq rfl
        (pinchedConstant_zero c.vertex)

lemma dgBarCompactEvaluationApexSpace_eq :
    (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up c.vertex))).obj =
      (dgBarCompactSpaceApex (dgBarCompactEvaluationPosetDiagram R D G x)
        (dgBarCompactEvaluationCocone R D G c x)).obj := by
  dsimp only [dgBarCompactSpaceApex, dgBarCompactEvaluationCocone]
  rw [JoinCocone.vertex_restrict, F2.Ind.mapJoinCocone_vertex, JoinCocone.ulift_vertex]

lemma dgBarCompactEvaluationLeg_eq (i : I) :
    dgBarCompactSpaceMapCast rfl (dgBarCompactEvaluationApexSpace_eq R D G c x)
      (dgBarCompactEvaluationEdgeValue R D x (dgBarCompactEvaluationLegEdge R D G c i)) =
        dgBarCompactSpaceLeg (dgBarCompactEvaluationPosetDiagram R D G x)
          (dgBarCompactEvaluationCocone R D G c x) i := by
  apply eq_of_heq
  apply (dgBarCompactSpaceMapCast_heq _ _ _).trans
  apply dgBarCompactSpaceEdgeValue_heq
  change (dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
    (ULift.up (dgBarCompactEvaluationLegEdge R D G c i).edge) =
      (F2.Compact.coconeTransportLeg (dgBarCompactEvaluationCocone R D G c x)
        (ULift.up (nerveEquiv.symm i))).edge
  rw [F2.Compact.coconeTransportLeg_edge]
  dsimp only [dgBarCompactEvaluationCocone]
  rw [dgBarCompactCoconeLeg_restrict, dgBarCompactCoconeLeg_map]
  change (dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
    (ULift.up (dgBarCompactEvaluationLegEdge R D G c i).edge) =
      (dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
        (((JoinCocone.ulift c).leg
          (SSet.yonedaEquiv.symm (ULift.up (ULift.up (nerveEquiv.symm i))))).edge)
  rw [dgBarCompactCoconeLeg_ulift]
  change _ = (dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
    (ULift.up (c.leg
      (SSet.yonedaEquiv.symm (ULift.up (nerveEquiv.symm i)))).edge)
  exact congrArg (fun e =>
    (dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌) (ULift.up e))
      (F2.Compact.coconeHomotopyLeg_edge c _)

end SerrePositivity.InfinityCategories

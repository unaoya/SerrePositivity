module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationEdgeNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.CoconeLegNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPointPost
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (x : D)

/-- 同じ任意の実余錐を、平坦化した添字上で評価する。 -/
def dgBarCompactEvaluationCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c)).restrict (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactIndexLiftIso.{u, v} (nerve I)).hom

abbrev dgBarCompactEvaluationStageVertex (i : I) :=
  G.app (Opposite.op ⦋0⦌) (ULift.up (nerveEquiv.symm i))

def dgBarCompactEvaluationIndexEdge {i j : I} (h : i ≤ j) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D).Edge
      (dgBarCompactEvaluationStageVertex R D G i) (dgBarCompactEvaluationStageVertex R D G j) :=
  (SSet.Edge.ofTruncated
    (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, max (u + 1) v} (CategoryTheory.nerve.edgeMk (homOfLE h)).toTruncated)).map G

lemma dgBarCompactEvaluationTransition_eq {i j : I} (h : i ≤ j) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceTransition (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x) h =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationEdgeValue R D x (dgBarCompactEvaluationIndexEdge R D G h) := by
  apply eq_of_heq
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceEdgeValue_heq
  rfl

def dgBarCompactEvaluationLegEdge (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D).Edge
      (dgBarCompactEvaluationStageVertex R D G i) c.vertex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c)
      (ULift.up (nerveEquiv.symm i))).ofEq rfl
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero c.vertex)

lemma dgBarCompactEvaluationApexSpace_eq :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up c.vertex))).obj =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceApex (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x)
        (dgBarCompactEvaluationCocone R D G c x)).obj := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceApex, dgBarCompactEvaluationCocone]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift_vertex]

lemma dgBarCompactEvaluationLeg_eq (i : I) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceMapCast rfl (dgBarCompactEvaluationApexSpace_eq R D G c x)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationEdgeValue R D x (dgBarCompactEvaluationLegEdge R D G c i)) =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceLeg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPosetDiagram R D G x)
          (dgBarCompactEvaluationCocone R D G c x) i := by
  apply eq_of_heq
  apply (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceMapCast_heq _ _ _).trans
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceEdgeValue_heq
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
    (ULift.up (dgBarCompactEvaluationLegEdge R D G c i).edge) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (dgBarCompactEvaluationCocone R D G c x)
        (ULift.up (nerveEquiv.symm i))).edge
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg_edge]
  dsimp only [dgBarCompactEvaluationCocone]
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoconeLeg_restrict, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoconeLeg_map]
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
    (ULift.up (dgBarCompactEvaluationLegEdge R D G c i).edge) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
        (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c).leg
          (SSet.yonedaEquiv.symm (ULift.up (ULift.up (nerveEquiv.symm i))))).edge)
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoconeLeg_ulift]
  change _ = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌)
    (ULift.up (c.leg
      (SSet.yonedaEquiv.symm (ULift.up (nerveEquiv.symm i)))).edge)
  exact congrArg (fun e =>
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app (Opposite.op ⦋1⦌) (ULift.up e))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeHomotopyLeg_edge c _)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

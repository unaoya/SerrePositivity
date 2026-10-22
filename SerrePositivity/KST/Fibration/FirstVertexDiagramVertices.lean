module
public import SerrePositivity.KST.Fibration.FirstVertexDiagramComponent
public import SerrePositivity.KST.Fibration.FunctorIsoValueComposition

/-! # 実対象図式の同じ初頂点値を、元の共同分類値で表示する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]

local instance : LeftFibration (pullback.snd p (transportSimplexFirstVertexMap B)) :=
  ⟨leftFibrations.pullback_snd p _ (LeftFibration.mem (p := p))⟩

/-- 元の実図式の初頂点値は、元の同じ共同分類値と一致する。 -/
theorem firstVertexDiagram_source_vertex (c : TransportSimplexCategory B) :
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
      leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c)) =
    (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
      (ULift.up (nerveVertex c)) (leftFibrationInfinityVertex p)).app (Opposite.op ⦋0⦌)
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (transportSimplexFirstVertexMap B) ≫ leftStraighteningSectionJointDiagram B)) := by
  let l := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B)
  let P := (pre l).app SpaceInfinity.{u}
  let F := leftStraighteningInfinityMap B ≫ P
  let a := ULift.up.{u + 1} (nerveVertex c)
  let x := leftFibrationInfinityVertex p
  have hs := congrArg (P.app (Opposite.op ⦋0⦌)) (leftStraighteningInfinityDiagram_vertex p)
  have hv := congrArg ((evaluateFunctorAt (Y := SpaceInfinity.{u}) a).app
    (Opposite.op ⦋0⦌)) hs
  have he := evaluateFunctorAt_functorVertex a (l ≫ leftStraighteningInfinityDiagram p)
  have hd := doubleFunctorEvaluation_vertex F x a
  exact he.symm.trans (hv.trans (hd.symm.trans
    (straighteningRestrict_source_vertex (leftFibrationObjectOf p) c)))

/-- 同じ実図式同型の頂点成分を元の二つの表示へ揃えると、同じ制限成分を回収する。 -/
theorem firstVertexDiagramValueIso_eq (c : TransportSimplexCategory B) :
    F2.isoNormalizeEndpoints
      (functorIsoValue (leftStraighteningInfinityDiagram_firstVertexIso p)
        (ULift.up (nerveVertex c)))
      (congrArg HomotopyCategory.mk (firstVertexDiagram_source_vertex p c))
      (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex
        (pullback.snd p (transportSimplexFirstVertexMap B)) c)) =
    firstVertexRestrictionChart (leftFibrationObjectOf p) c :=
  F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    ((functorIsoValue_heq_map _ _).trans (firstVertexDiagramIso_heq_restrictionChart p c))

end SerrePositivity.KST.Fibration

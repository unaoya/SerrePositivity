module
public import SerrePositivity.KST.Fibration.FirstVertexOppositeChart

/-! # 元の実分類図式の初頂点 transport 同型は、同じ反転点を追跡した指定成分 -/

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

/-- 元の対象別 transport 同型は、元の解像上の同型の指定対象成分。 -/
theorem firstVertexTransportDiagramIso_heq_app :
    HEq (leftStraighteningInfinityDiagram_firstVertexTransportIso p)
      ((leftStraighteningInfinityMap_firstVertexOppositeIso B).app
        (coherentNerveVertex (firstVertexComparisonObject p))) := by
  let k := transportSimplexFirstVertexMap B
  let P := (pre ((SSet.uliftFunctor.{u + 1, u}).map k)).app SpaceInfinity.{u}
  have hs := (congrArg ((leftStraighteningInfinityMap B ≫ P).app (Opposite.op ⦋0⦌))
    (firstVertexComparisonObject_projection_vertex p)).trans
      (congrArg (P.app (Opposite.op ⦋0⦌)) (leftStraighteningInfinityDiagram_vertex p).symm)
  have ht := (congrArg ((leftStraighteningOppositeCoherentMap (TransportSimplexCategory B)).app
    (Opposite.op ⦋0⦌)) (firstVertexOppositeBaseChange_vertex p)).trans
      (leftStraighteningOppositeCoherentMap_vertex (pullback.snd p k))
  unfold leftStraighteningInfinityDiagram_firstVertexTransportIso
  exact F2.iso_endpoints_heq _ (congrArg HomotopyCategory.mk hs)
    (congrArg HomotopyCategory.mk ht)

/-- 元の実対象図式の transport 成分は、同じ厳密切断の反転点を保持する指定成分。 -/
theorem firstVertexTransportDiagramIso_heq_oppositeChart (c : TransportSimplexCategory B) :
    HEq (VertexIso.map (leftStraighteningInfinityDiagram_firstVertexTransportIso p)
      (evaluateFunctorAt (ULift.up (nerveVertex c))))
      (firstVertexOppositeChart p c) := by
  let k := transportSimplexFirstVertexMap B
  let P := (pre ((SSet.uliftFunctor.{u + 1, u}).map k)).app SpaceInfinity.{u}
  let e := leftStraighteningInfinityMap_firstVertexOppositeIso B
  let x := coherentNerveVertex (firstVertexComparisonObject p)
  let a := ULift.up.{u + 1} (nerveVertex c)
  have hs : functorVertex ((SSet.uliftFunctor.map k) ≫ leftStraighteningInfinityDiagram p) =
      (edgewiseEnrichedInfinityMap (LeftFibrationObject B) ≫
        leftStraighteningInfinityMap B ≫ P).app (Opposite.op ⦋0⦌) x :=
    ((congrArg ((leftStraighteningInfinityMap B ≫ P).app (Opposite.op ⦋0⦌))
      (firstVertexComparisonObject_projection_vertex p)).trans
        (congrArg (P.app (Opposite.op ⦋0⦌)) (leftStraighteningInfinityDiagram_vertex p).symm)).symm
  have ht : functorVertex (leftCoherentTransport (pullback.snd p k)) =
      (leftFibrationEdgewiseFirstVertexBaseChange B ≫
        leftStraighteningOppositeCoherentMap (TransportSimplexCategory B)).app
          (Opposite.op ⦋0⦌) x :=
    ((congrArg ((leftStraighteningOppositeCoherentMap (TransportSimplexCategory B)).app
      (Opposite.op ⦋0⦌)) (firstVertexOppositeBaseChange_vertex p)).trans
        (leftStraighteningOppositeCoherentMap_vertex (pullback.snd p k))).symm
  have hm := F2.vertexIso_map_heq_of_heq
    (leftStraighteningInfinityDiagram_firstVertexTransportIso p) (e.app x) hs ht
    (firstVertexTransportDiagramIso_heq_app p) (evaluateFunctorAt a)
  have ha := F2.vertexIso_map_heq_of_heq (e.app x)
    (VertexIso.map e (evaluateFunctorAt x))
    (evaluateFunctorAt_functorVertex x _).symm
    (evaluateFunctorAt_functorVertex x _).symm
    (F2.functorIso_app_heq_evaluate e x) (evaluateFunctorAt a)
  exact hm.trans (ha.trans ((heq_of_eq (F2.vertexIso_map_comp e
    (evaluateFunctorAt x) (evaluateFunctorAt a))).trans
      (firstVertexOppositeChart_heq_doubleMap p c).symm))

end SerrePositivity.KST.Fibration

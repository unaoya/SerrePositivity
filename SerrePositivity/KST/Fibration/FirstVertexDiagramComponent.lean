module
public import SerrePositivity.KST.Fibration.FirstVertexStrictSection

/-! # 元の実対象図式の初頂点制限同型を、同じ指定切断成分へ照合する -/

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

/-- 実対象図式の元の初頂点同型は、同じ全対象同型の指定対象成分。 -/
theorem firstVertexDiagramIso_heq_app :
    HEq (leftStraighteningInfinityDiagram_firstVertexIso p)
      ((leftStraighteningInfinityMap_firstVertexRestrictionIso B).app
        (leftFibrationInfinityVertex p)) := by
  let k := transportSimplexFirstVertexMap B
  let P := (pre ((SSet.uliftFunctor.{u + 1, u}).map k)).app SpaceInfinity.{u}
  have hs := congrArg (P.app (Opposite.op ⦋0⦌)) (leftStraighteningInfinityDiagram_vertex p)
  have ht := (congrArg ((leftStraighteningCoherentMap (TransportSimplexCategory B)).app
    (Opposite.op ⦋0⦌)) (leftFibrationInfinityBaseChange_vertex k
      (leftFibrationObjectOf p))).trans (leftStraighteningCoherentMap_vertex (pullback.snd p k))
  unfold leftStraighteningInfinityDiagram_firstVertexIso
  exact F2.iso_endpoints_heq _ (congrArg HomotopyCategory.mk hs).symm
    (congrArg HomotopyCategory.mk ht)

/-- 元の実図式の初頂点制限成分は、元の切断点を追跡した同じ指定成分そのもの。 -/
theorem firstVertexDiagramIso_heq_restrictionChart (c : TransportSimplexCategory B) :
    HEq (VertexIso.map (leftStraighteningInfinityDiagram_firstVertexIso p)
      (evaluateFunctorAt (ULift.up (nerveVertex c))))
      (firstVertexRestrictionChart (leftFibrationObjectOf p) c) := by
  let k := transportSimplexFirstVertexMap B
  let U := SSet.uliftFunctor.{u + 1, u}
  let P := (pre (U.map k)).app SpaceInfinity.{u}
  let e := leftStraighteningInfinityMap_firstVertexRestrictionIso B
  let x := leftFibrationInfinityVertex p
  let a := ULift.up.{u + 1} (nerveVertex c)
  have hs : functorVertex (U.map k ≫ leftStraighteningInfinityDiagram p) =
      (leftStraighteningInfinityMap B ≫ P).app (Opposite.op ⦋0⦌) x :=
    congrArg (P.app (Opposite.op ⦋0⦌)) (leftStraighteningInfinityDiagram_vertex p)
  have ht : functorVertex (leftStraighteningCandidate (pullback.snd p k)) =
      (leftFibrationInfinityBaseChange k ≫
        leftStraighteningCoherentMap (TransportSimplexCategory B)).app (Opposite.op ⦋0⦌) x :=
    ((congrArg ((leftStraighteningCoherentMap (TransportSimplexCategory B)).app
      (Opposite.op ⦋0⦌)) (leftFibrationInfinityBaseChange_vertex k
        (leftFibrationObjectOf p))).trans
          (leftStraighteningCoherentMap_vertex (pullback.snd p k))).symm
  have hm := F2.vertexIso_map_heq_of_heq (leftStraighteningInfinityDiagram_firstVertexIso p)
    (e.app x) hs ht (firstVertexDiagramIso_heq_app p) (evaluateFunctorAt a)
  have ha := F2.vertexIso_map_heq_of_heq (e.app x)
    (VertexIso.map e (evaluateFunctorAt x))
    (evaluateFunctorAt_functorVertex x _).symm
    (evaluateFunctorAt_functorVertex x _).symm
    (F2.functorIso_app_heq_evaluate e x) (evaluateFunctorAt a)
  exact hm.trans (ha.trans ((heq_of_eq (F2.vertexIso_map_comp e
    (evaluateFunctorAt x) (evaluateFunctorAt a))).trans
      (firstVertexRestrictionChart_heq_doubleMap (leftFibrationObjectOf p) c).symm))

end SerrePositivity.KST.Fibration

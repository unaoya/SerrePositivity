module

public import SerrePositivity.InfinityCategories.F2.Compact.UniverseRepresentation
public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationEdgeDetection
public import SerrePositivity.InfinityCategories.F1.Universe.Transport
public import SerrePositivity.InfinityCategories.F1.Universe.Reflection

/-!
概要：指定された空間の宇宙変更は、元の同じ辺の可逆性を反映する。
方針：元の普遍射影の持ち上げの同じ表現で輸送を検出し、Kan fiber の宇宙比較を戻す。
規約：元の spaceUniverseDiagram と指定辺を保持する。
使われ方：Ind-S の小極限・小余極限の反映を同じ宇宙変更について検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 概要：指定宇宙変更での像が可逆な元の辺は可逆。
方針：普遍 left fibration の輸送と Kan fiber の宇宙反映。
規約：指定辺自身の判定。使われ方：同じ写像の小極限・小余極限の反映。 -/
lemma spaceUniverseDiagram_reflects_invertibleEdge
    {a b : SpaceInfinity.{u} _⦋0⦌} (e : SpaceInfinity.{u}.Edge a b)
    (he : IsInvertibleEdge ((uliftTruncatedEdge.{u + 1, u + 2} e).map
      ((truncation 2).map spaceUniverseDiagram.{u}))) : IsInvertibleEdge e := by
  let p := leftUnstraighteningProjection (𝟙 SpaceInfinity.{u})
  let R := spaceUniverseTransportRepresentation (𝟙 SpaceInfinity.{u})
  have hD : R.diagram = spaceUniverseDiagram.{u} := by
    change (SSet.uliftFunctor.{u + 2, u + 1}).map (𝟙 SpaceInfinity.{u}) ≫ _ = _
    rw [(SSet.uliftFunctor.{u + 2, u + 1}).map_id, Category.id_comp]
  have hR : IsInvertibleEdge
      ((uliftTruncatedEdge.{u + 1, u + 2} e).map ((truncation 2).map R.diagram)) := by
    have hE : ((uliftTruncatedEdge.{u + 1, u + 2} e).map
        ((truncation 2).map R.diagram)).edge =
        ((uliftTruncatedEdge.{u + 1, u + 2} e).map
          ((truncation 2).map spaceUniverseDiagram.{u})).edge :=
      congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) (ULift.up e.edge)) hD
    exact (isInvertibleEdge_congr hE).mpr he
  have hT := (R.transport_isQCatEquivalence_iff_invertible
    (uliftTruncatedEdge.{u + 1, u + 2} e)).mpr hR
  have hU : IsQCatEquivalence (uliftFiberTransport.{u + 1, u + 2} p (edgeTransport p e)) :=
    hT.ofFunctorIso (edgeTransport_uliftIso p e)
  let iA := uliftVertexFiberIso.{u + 1, u + 2} p a
  let iB := uliftVertexFiberIso.{u + 1, u + 2} p b
  have hA := (qCatEquivalenceOfIso iA.symm).isQCatEquivalence
  have hB := (qCatEquivalenceOfIso iB).isQCatEquivalence
  have hV : IsQCatEquivalence
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (edgeTransport p e)) :=
    hB.cancel_right (hA.cancel_left hU)
  have h := (isQCatEquivalence_ulift_iff_of_kan.{u + 1, u + 2} (edgeTransport p e)).mp hV
  have hP := (edgeTransport_pullback_isQCatEquivalence_iff
    pointedSpaceProjection (𝟙 SpaceInfinity.{u}) e).mp h
  exact (isInvertibleEdge_congr
    (show (e.map (𝟙 SpaceInfinity.{u})).edge = e.edge from rfl)).mp
      (pointedSpaceEdge_isInvertible_of_transport_isQCatEquivalence _ hP)
/-- 概要：指定宇宙変更は、持ち上げた空間圏の任意の元の辺の可逆性を反映する。
方針：同じ一単体の ULift を外して戻す。規約：元の辺。使われ方：native な余錐比較。 -/
lemma spaceUniverseDiagram_reflects_invertibleEdge_native
    {a b : ((SSet.uliftFunctor.{u + 2, u + 1}).obj SpaceInfinity.{u}) _⦋0⦌}
    (e : ((SSet.uliftFunctor.{u + 2, u + 1}).obj SpaceInfinity.{u}).Edge a b)
    (he : IsInvertibleEdge (e.map spaceUniverseDiagram.{u})) : IsInvertibleEdge e := by
  let e₀ : SpaceInfinity.{u}.Edge a.down b.down :=
    ⟨e.edge.down, congrArg ULift.down e.src_eq, congrArg ULift.down e.tgt_eq⟩
  have h : uliftTruncatedEdge.{u + 1, u + 2} e₀ = e.toTruncated := by
    apply Truncated.Edge.ext
    rfl
  have hi : IsInvertibleEdge ((uliftTruncatedEdge.{u + 1, u + 2} e₀).map
      ((truncation 2).map spaceUniverseDiagram.{u})) := by
    rw [h]
    exact he
  have h₀ := (spaceUniverseDiagram_reflects_invertibleEdge e₀ hi).ulift.{u + 1, u + 2}
  rw [h] at h₀
  exact h₀
end SerrePositivity.InfinityCategories.F2.Compact

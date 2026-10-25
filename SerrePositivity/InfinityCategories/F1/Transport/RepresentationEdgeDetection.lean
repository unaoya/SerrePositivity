module

public import SerrePositivity.InfinityCategories.F1.Transport.WitnessEdges
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationTransportNaturality
public import SerrePositivity.InfinityCategories.F1.Fibrations.PullbackTransport
public import SerrePositivity.InfinityCategories.F1.Transport.InvertibleLeftTransport

/-!
概要：元の left fibration の輸送の同値性を、同じ表現図式の元の辺の可逆性で判定する。
方針：元の比較射の両端 fiber 同値と、普遍 pointed-space 射影の輸送を使う。
規約：元の表現と指定辺を保持し、底の quasicategory 性を要求しない。
使われ方：表現可能前層の反対辺作用から元の Hom 前合成の局所性を検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 概要：同じ表現の辺の可逆性と元の輸送の同値性は同値。
方針：両端の fiber 比較で普遍輸送へ戻す。
規約：元の指定辺と表現を保持。使われ方：Ind-S の実辺作用の検出。 -/
lemma LeftTransportRepresentation.transport_isQCatEquivalence_iff_invertible
    {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    (R : LeftTransportRepresentation p) {a b : B _⦋0⦌} (e : B.Edge a b) :
    IsQCatEquivalence (edgeTransport p e) ↔ IsInvertibleEdge (e.map R.diagram) := by
  have h := (leftFibrationMap_transport_isQCatEquivalence_iff p
    (leftUnstraighteningProjection R.diagram) R.comparison R.over_base e
    (R.fiber_equivalence a) (R.fiber_equivalence b)).trans
      (edgeTransport_pullback_isQCatEquivalence_iff pointedSpaceProjection R.diagram e)
  exact h.trans ⟨pointedSpaceEdge_isInvertible_of_transport_isQCatEquivalence _,
    edgeTransport_isQCatEquivalence_of_isInvertibleEdge pointedSpaceProjection _⟩
end SerrePositivity.InfinityCategories

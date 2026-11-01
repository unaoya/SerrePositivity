module

public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationEdgeDetection
public import
  SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.F1.Universe.Transport
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence
public import SerrePositivity.InfinityCategories.F1.Universe.Reflection
public import SerrePositivity.InfinityCategories.F1.Coherent.SmallCoherentStraightening
public import SerrePositivity.InfinityCategories.F1B.FunctorIsoConstantEdges

/-!
概要：元の小さい left fibration の分類図式が辺を反転すれば、同じ辺の輸送は同値。
方針：表現の分類辺判定を用い、fiber の宇宙移送を反映する。
規約：D の汎用補題はコーディネータ許可による読み取り専用 import。
使われ方：元の表現可能前層の反対辺作用による Hom 前合成の局所性判定。
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
/-- 概要：元の分類辺の可逆性は元の同じ fiber 輸送の同値性を与える。
方針：表現比較と宇宙反映。規約：元の辺。使われ方：表現可能前層の局所性。 -/
lemma leftStraighteningInfinityDiagram_transport_of_invertible {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (e : B.Edge a b)
    (he : IsInvertibleEdge ((uliftTruncatedEdge.{u, u + 1} e).map
      ((truncation 2).map (leftStraighteningInfinityDiagram p)))) :
    IsQCatEquivalence (edgeTransport p e) := by
  letI : ∀ m, Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj E).obj m) :=
    fun m ↦ inferInstanceAs (Small.{u} (ULift.{u + 1} (E.obj m)))
  let R := smallLeftStraighteningRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)
  have hR := functorIso_map_isInvertible_of_map
    (leftStraighteningInfinityDiagram_representationIso p R).symm
    (uliftTruncatedEdge.{u, u + 1} e) he
  have hT := (R.transport_isQCatEquivalence_iff_invertible
    (uliftTruncatedEdge.{u, u + 1} e)).mpr hR
  have hU : IsQCatEquivalence (uliftFiberTransport.{u, u + 1} p (edgeTransport p e)) :=
    hT.ofFunctorIso (edgeTransport_uliftIso p e)
  have hA := (qCatEquivalenceOfIso (uliftVertexFiberIso.{u, u + 1} p a).symm).isQCatEquivalence
  have hB := (qCatEquivalenceOfIso (uliftVertexFiberIso.{u, u + 1} p b)).isQCatEquivalence
  have hV : IsQCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).map (edgeTransport p e)) :=
    hB.cancel_right (hA.cancel_left hU)
  exact (isQCatEquivalence_ulift_iff_of_kan.{u, u + 1} (edgeTransport p e)).mp hV

end SerrePositivity.InfinityCategories

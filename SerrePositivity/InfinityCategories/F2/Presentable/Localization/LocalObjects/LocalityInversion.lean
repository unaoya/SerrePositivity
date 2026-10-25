module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.Definition
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableInversionLocality

/-!
概要：既存の写像空間の局所性を元の表現可能前層の辺反転で判定する。
方針：同じ前合成円柱と slice 輸送を両方向に比較し、分類輸送の可逆性へ移す。
規約：元の辺と元の前合成を保持する。
使われ方：全共変 Hom 関手間の比較を使う filtered 閉性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
open HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：元の局所前合成が同値なら同じ反対 slice 輸送も同値。
方針：元の前合成円柱の比較で両端の fiber 同型を消去する。
規約：元の前合成の同値性を使用する。
使われ方：局所性から分類辺の反転を得る。 -/
lemma oppositeSliceTransport_isQCatEquivalence_of_local
    {C : SSet.{u}} [Quasicategory C] (z : C _⦋0⦌) {x y : C _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj C) x y)
    (h : IsLocalForHom (Truncated.HomotopyCategory.homMk e) z) :
    IsQCatEquivalence (edgeTransport
      (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm z))) (edgeOp e)) := by
  obtain ⟨H, h₀, h₁, hp⟩ := pinchedPrecompose_slicePrism_exists z e
  have hc := F1B.isQCatEquivalence_op h
  have hi := hc.comp (qCatEquivalenceOfIso (pinchedOppositeSliceFiberIso z x)).isQCatEquivalence
  have hj := hi.ofFunctorIso (pinchedSlicePrism_oppositeTransportIso z e _ H h₀ h₁ hp)
  exact (qCatEquivalenceOfIso (pinchedOppositeSliceFiberIso z y)).isQCatEquivalence.cancel_left hj

/-- 概要：局所性は同じ元の表現可能前層による指定反対辺の反転と同値。
方針：元の slice 輸送の比較、宇宙持ち上げ、分類辺の可逆性判定を使う。
規約：前層や辺の同型な代表を選び直さない。
使われ方：局所性を全 Hom 関手の自然比較成分として扱う。 -/
lemma isLocalForHom_iff_representableInverts
    {C : SSet.{u}} [Quasicategory C] (z : C _⦋0⦌) {x y : C _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj C) x y) :
    IsLocalForHom (Truncated.HomotopyCategory.homMk e) z ↔
      IsInvertibleEdge ((uliftTruncatedEdge.{u, u + 1} (edgeOp e)).map
        ((truncation 2).map (representablePresheafInfinity z))) := by
  constructor
  · intro h
    let p := SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm z))
    let d := SSet.Edge.ofTruncated (X := C.op) (edgeOp e)
    have ht : IsQCatEquivalence (edgeTransport p d) :=
      oppositeSliceTransport_isQCatEquivalence_of_local z e h
    have hU := (isQCatEquivalence_ulift_iff_of_kan.{u, u + 1} (edgeTransport p d)).mpr ht
    have hA := (qCatEquivalenceOfIso
      (uliftVertexFiberIso.{u, u + 1} p (SSet.opObjEquiv.symm y)).symm).isQCatEquivalence
    have hB := (qCatEquivalenceOfIso
      (uliftVertexFiberIso.{u, u + 1} p (SSet.opObjEquiv.symm x))).isQCatEquivalence
    have hv : IsQCatEquivalence (uliftFiberTransport.{u, u + 1} p (edgeTransport p d)) :=
      hA.comp (hU.comp hB)
    have hT := hv.ofFunctorIso (edgeTransport_uliftIso p d).symm
    have : ∀ m, Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj
        (sliceOver (SSet.yonedaEquiv.symm z)).op).obj m) := fun m ↦
      inferInstanceAs (Small.{u}
        (ULift.{u + 1} ((sliceOver (SSet.yonedaEquiv.symm z)).op.obj m)))
    let R := smallLeftStraighteningRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)
    have hR := (R.transport_isQCatEquivalence_iff_invertible
      (uliftTruncatedEdge.{u, u + 1} d)).mp hT
    have hS := functorIso_map_isInvertible_of_map
      (leftStraighteningInfinityDiagram_representationIso p R)
      (uliftTruncatedEdge.{u, u + 1} d) hR
    exact functorIso_map_isInvertible_of_map (representablePresheafInfinity_sliceIso z)
      (uliftTruncatedEdge.{u, u + 1} (edgeOp e)) hS
  · exact representablePresheafInfinity_precompose_isQCatEquivalence_of_invertible z e

end SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects

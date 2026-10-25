module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.ClassifierTransportInversion
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafSliceComparison

/-!
概要：元の表現可能前層が反対辺を反転すれば、元の表現可能 slice の反対輸送は同値。
方針：同じ前層の slice 分類比較を分類辺の輸送判定へ接続する。
規約：別の Hom 前層や指定辺を選ばない。
使われ方：表現可能前層の反対辺作用から Hom 前合成の局所性を判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 概要：同じ表現可能前層の反対辺像が可逆なら、元の slice の反対輸送は同値。
方針：全分類比較と輸送の反映。規約：元の辺。使われ方：局所性判定の入力。 -/
lemma representablePresheafInfinity_transport_of_invertible {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) {x y : C _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj C) x y)
    (he : IsInvertibleEdge ((uliftTruncatedEdge.{u, u + 1} (edgeOp e)).map
      ((truncation 2).map (representablePresheafInfinity z)))) :
    IsQCatEquivalence (edgeTransport
      (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm z)))
      (SSet.Edge.ofTruncated (X := C.op) (edgeOp e))) := by
  apply leftStraighteningInfinityDiagram_transport_of_invertible
  exact functorIso_map_isInvertible_of_map (representablePresheafInfinity_sliceIso z).symm
    (uliftTruncatedEdge.{u, u + 1} (edgeOp e)) he

end SerrePositivity.InfinityCategories

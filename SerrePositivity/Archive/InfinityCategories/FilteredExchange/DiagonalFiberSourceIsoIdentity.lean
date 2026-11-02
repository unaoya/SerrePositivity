module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalFiberSourceIsoAction

/-!
概要：元の恒等始点比較の対角輸送は、同じ native 終点の恒等比較。
方針：元の関手空間作用への像に戻し、恒等同型の像を計算する。
規約：sourceIso を再選択しない。使われ方：固定底辺の下二頂点比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の恒等始点比較の sourceIso は同じ実対角輸送の恒等同型。 -/
lemma diagonalFiberTransport_sourceIso_refl {P E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a b) :
    diagonalFiberTransport_sourceIso p (Iso.refl (SSet.HomotopyCategory.mk (functorVertex f))) c =
      Iso.refl _ := by
  let Ω := functorPairRight c ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint
  have hm := diagonalFiberTransport_sourceIso_heq_action p (Iso.refl
    (SSet.HomotopyCategory.mk (functorVertex f))) c
  have hmap : VertexIso.map (Iso.refl (SSet.HomotopyCategory.mk (functorVertex f))) Ω =
      Iso.refl _ := by apply Iso.ext; exact (hoFunctor.map Ω).toFunctor.map_id _
  rw [hmap] at hm
  have hvertex := diagonalFiberSourceAction_vertex p f c
  change Ω.app (Opposite.op ⦋0⦌) (functorVertex f) = _ at hvertex
  exact eq_of_heq (hm.trans (by rw [hvertex]))

end SerrePositivity.InfinityCategories.F2

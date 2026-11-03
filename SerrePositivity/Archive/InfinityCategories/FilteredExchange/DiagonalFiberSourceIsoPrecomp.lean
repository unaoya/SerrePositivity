module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalFiberSourceActionPrecomp

/-!
概要：元の指定始点同型の輸送は、全係数を制限しても同じ指定値を与える。
方針：元の sourceIso を同じ一つの関手空間作用の像へ戻す。
規約：指定同型の選択を保持。使われ方：高次図式の実面の係数制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定 sourceIso の前合成は、元の始点同型と区間を制限した指定 sourceIso と一致する。 -/
lemma diagonalFiberTransport_sourceIso_precomp_heq {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    {f g : P ⟶ vertexFiber p a} (e : FunctorIso f g)
    (c : P ⟶ intervalMappingSpace a b) (q : Q ⟶ P) :
    HEq ((diagonalFiberTransport_sourceIso p e c).precomp q)
      (diagonalFiberTransport_sourceIso p (e.precomp q) (q ≫ c)) := by
  let A := functorPairRight c ≫
    (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint
  let A' := functorPairRight (q ≫ c) ≫
    (ihom Q).map (parametrizedFiberTransportFamily p a b).endpoint
  have he := diagonalFiberTransport_sourceIso_heq_action p e c
  have hs := (diagonalFiberSourceAction_vertex p f c).symm
  have ht := (diagonalFiberSourceAction_vertex p g c).symm
  have hleft := vertexIso_map_heq_of_heq (diagonalFiberTransport_sourceIso p e c)
    (VertexIso.map e A) hs ht he ((pre q).app (vertexFiber p b))
  have hc : A ≫ (pre q).app (vertexFiber p b) =
      (pre q).app (vertexFiber p a) ≫ A' := diagonalFiberSourceAction_precomp p c q
  have hmid := (heq_of_eq (vertexIso_map_comp e A ((pre q).app (vertexFiber p b)))).trans
    ((vertexIso_map_heq e hc).trans
      (heq_of_eq (vertexIso_map_comp e ((pre q).app (vertexFiber p a)) A')).symm)
  have hright := diagonalFiberTransport_sourceIso_heq_action p (e.precomp q) (q ≫ c)
  rw [functorIso_precomp_eq_mapIso] at hright
  rw [functorIso_precomp_eq_mapIso]
  exact hleft.trans (hmid.trans hright.symm)

end SerrePositivity.InfinityCategories.F2

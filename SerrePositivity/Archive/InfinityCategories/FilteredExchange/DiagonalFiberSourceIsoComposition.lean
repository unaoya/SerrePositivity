module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalFiberSourceIsoAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence

/-!
概要：元の始点同型の対角輸送は、元の指定同型の合成を厳密に保つ。
方針：同じ全区間作用の関手像へ三つの指定比較を戻す。
規約：sourceIso の選択を保持。使われ方：合成四角形の中間比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定始点比較の合成は、同じ区間の元の sourceIso の合成へ送られる。 -/
lemma diagonalFiberTransport_sourceIso_trans {P E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    {f g h : P ⟶ vertexFiber p a} (e : FunctorIso f g) (d : FunctorIso g h)
    (c : P ⟶ intervalMappingSpace a b) :
    diagonalFiberTransport_sourceIso p e c ≪≫ diagonalFiberTransport_sourceIso p d c =
      diagonalFiberTransport_sourceIso p (e ≪≫ d) c := by
  let Ω := functorPairRight c ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint
  have hf := (diagonalFiberSourceAction_vertex p f c).symm
  have hg := (diagonalFiberSourceAction_vertex p g c).symm
  have hh := (diagonalFiberSourceAction_vertex p h c).symm
  have he := diagonalFiberTransport_sourceIso_heq_action p e c
  have hd := diagonalFiberTransport_sourceIso_heq_action p d c
  have hc := diagonalFiberTransport_sourceIso_heq_action p (e ≪≫ d) c
  exact eq_of_heq ((vertexIso_trans_heq_of_heq _ _ (VertexIso.map e Ω)
    (VertexIso.map d Ω) hf hg hh he hd).trans
      ((heq_of_eq (vertexIso_map_trans e d Ω).symm).trans hc.symm))

end SerrePositivity.InfinityCategories.F2

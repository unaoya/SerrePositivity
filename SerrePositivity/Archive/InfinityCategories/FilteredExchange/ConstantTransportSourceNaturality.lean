module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantTransportSourceActionIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoComponentNaturality

/-!
概要：元の定値輸送比較は、元の指定始点同型と自然な正方形をなす。
方針：同じ全定値作用の関手同型の自然性を、元の指定成分へ戻す。
規約：全係数と元の比較を保持。使われ方：定値終辺の消去と始点比較の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の定値輸送比較は、同じ元の sourceIso と元の始点同型に自然である。 -/
lemma diagonalFiberTransport_constantIso_source_naturality {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a : B _⦋0⦌}
    {f g : P ⟶ vertexFiber p a} (e : FunctorIso f g)
    (c : P ⟶ intervalMappingSpace a a) (hc : intervalMappingUncurry c = SSet.const a) :
    diagonalFiberTransport_sourceIso p e c ≪≫ diagonalFiberTransport_constantIso p g c hc =
      diagonalFiberTransport_constantIso p f c hc ≪≫ e := by
  have h := functorIso_app_vertexIso_naturality (diagonalConstantTransportSourceActionIso p c hc) e
  have hId : HEq (VertexIso.map e (𝟙 _)) e := by
    have hi : (hoFunctor.map (𝟙 ((ihom P).obj (vertexFiber p a)))).toFunctor =
        𝟭 (SSet.HomotopyCategory ((ihom P).obj (vertexFiber p a))) := by
      rw [CategoryTheory.Functor.map_id]
      rfl
    exact mapIso_heq_of_functor_eq hi e
  exact vertexIso_square_of_heq _ _ _ _ _ _ _ _
    (diagonalFiberSourceAction_vertex p f c) (diagonalFiberSourceAction_vertex p g c)
    rfl rfl (diagonalFiberTransport_sourceIso_heq_action p e c).symm
    (diagonalConstantTransportSourceActionIso_app_heq p c hc g)
    (diagonalConstantTransportSourceActionIso_app_heq p c hc f) hId h

end SerrePositivity.InfinityCategories.F2

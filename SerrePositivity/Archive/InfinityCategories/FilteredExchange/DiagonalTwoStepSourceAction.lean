module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalTwoStepComparisonPrecomp

/-!
概要：同じ二段対角輸送の始点作用を、一つの関手空間の射で保持する。
方針：二つの元の全区間作用を同じ順に合成する。
規約：全係数と指定 sourceIso を保持。使われ方：四角形の始点自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二つの全区間の始点作用を同じ順に合成する射。 -/
def diagonalTwoStepSourceAction {E B P : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b c : B _⦋0⦌} (l : P ⟶ intervalMappingSpace a b)
    (r : P ⟶ intervalMappingSpace b c) :
    (ihom P).obj (vertexFiber p a) ⟶ (ihom P).obj (vertexFiber p c) :=
  (functorPairRight l ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint) ≫
    (functorPairRight r ≫ (ihom P).map (parametrizedFiberTransportFamily p b c).endpoint)

/-- 元の二段始点作用の頂点は、同じ元の二段対角輸送の頂点。 -/
lemma diagonalTwoStepSourceAction_vertex {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (l : P ⟶ intervalMappingSpace a b)
    (r : P ⟶ intervalMappingSpace b c) :
    ((functorPairRight l ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint) ≫
      (functorPairRight r ≫ (ihom P).map (parametrizedFiberTransportFamily p b c).endpoint)).app
      (Opposite.op ⦋0⦌) (functorVertex f) =
        functorVertex (diagonalFiberTransport p (diagonalFiberTransport p f l) r) := by
  change (functorPairRight r ≫ (ihom P).map _).app _
    ((functorPairRight l ≫ (ihom P).map _).app _ (functorVertex f)) = _
  rw [diagonalFiberSourceAction_vertex, diagonalFiberSourceAction_vertex]

/-- 元の二段 sourceIso は、同じ一つの全二段作用による指定像である。 -/
lemma diagonalFiberTransport_sourceIso_two_heq_action {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c : B _⦋0⦌}
    {f g : P ⟶ vertexFiber p a} (e : FunctorIso f g)
    (l : P ⟶ intervalMappingSpace a b) (r : P ⟶ intervalMappingSpace b c) :
    HEq (diagonalFiberTransport_sourceIso p (diagonalFiberTransport_sourceIso p e l) r)
      (VertexIso.map e
        ((functorPairRight l ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint) ≫
          (functorPairRight r ≫ (ihom P).map
            (parametrizedFiberTransportFamily p b c).endpoint))) := by
  let L := functorPairRight l ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint
  let R := functorPairRight r ≫ (ihom P).map (parametrizedFiberTransportFamily p b c).endpoint
  have h := vertexIso_map_heq_of_heq (diagonalFiberTransport_sourceIso p e l)
    (VertexIso.map e L) (diagonalFiberSourceAction_vertex p f l).symm
    (diagonalFiberSourceAction_vertex p g l).symm
    (diagonalFiberTransport_sourceIso_heq_action p e l) R
  exact (diagonalFiberTransport_sourceIso_heq_action p
    (diagonalFiberTransport_sourceIso p e l) r).trans
      (h.trans (heq_of_eq (vertexIso_map_comp e L R)))

end SerrePositivity.InfinityCategories.F2

module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantTransportSourceNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareSourceNaturality
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareConstantTopPrecomp

/-!
概要：元の定値終辺を消去した四角形比較は、同じ元の始点同型に自然である。
方針：四角形比較の始点正方形と、元の定値輸送比較の正方形を貼る。
規約：二つの元の指定因子を保持。使われ方：元の合成輸送の中間始点比較の移動。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の constantTopIso は、元の二段 sourceIso と残りの一段 sourceIso に自然。 -/
lemma transportIntervalSquare_constantTopIso_source_naturality {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b d : B _⦋0⦌}
    (s : TransportIntervalSquare P a b d d)
    (hs : intervalMappingUncurry s.top = SSet.const d)
    {f g : P ⟶ vertexFiber p a} (e : FunctorIso f g) :
    diagonalFiberTransport_sourceIso p (diagonalFiberTransport_sourceIso p e s.bottom) s.right ≪≫
        s.constantTopIso p g hs =
      s.constantTopIso p f hs ≪≫ diagonalFiberTransport_sourceIso p e s.left := by
  have h := transportIntervalSquare_transportIso_source_naturality p s e
  have hc := diagonalFiberTransport_constantIso_source_naturality p
    (diagonalFiberTransport_sourceIso p e s.left) s.top hs
  unfold TransportIntervalSquare.constantTopIso
  rw [← Iso.trans_assoc, h, Iso.trans_assoc, hc, ← Iso.trans_assoc]

end SerrePositivity.InfinityCategories.F2

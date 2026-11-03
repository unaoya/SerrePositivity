module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantTransportPrecomp
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareChosenPrecomp

/-!
概要：定値終辺を消去した元の四角形比較は、全係数制限を保つ。
方針：元の transportIso と元の定値輸送比較の制限則を貼り合わせる。
規約：二つの元の指定因子を保持。使われ方：元の Kan 合成輸送の係数自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の constantTopIso の係数制限は、制限後の同じ元の指定比較の値を保つ。 -/
lemma transportIntervalSquare_constantTopIso_precomp_heq {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b d : B _⦋0⦌}
    (s : TransportIntervalSquare P a b d d) (f : P ⟶ vertexFiber p a)
    (hs : intervalMappingUncurry s.top = SSet.const d) (q : Q ⟶ P)
    (hs' : intervalMappingUncurry (s.precomp q).top = SSet.const d) :
    HEq ((s.constantTopIso p f hs).precomp q)
      ((s.precomp q).constantTopIso p (q ≫ f) hs') := by
  have h := transportIntervalSquare_transportIso_precomp_heq p s f q
  have hconst := diagonalFiberTransport_constantIso_precomp_heq_of_input p
    (diagonalFiberTransport p f s.left) s.top hs q hs'
    (diagonalFiberTransport p (q ≫ f) (q ≫ s.left))
    (diagonalFiberTransport_precomp p f s.left q)
  rw [TransportIntervalSquare.constantTopIso, TransportIntervalSquare.constantTopIso,
    functorIso_precomp_trans]
  exact vertexIso_trans_heq_of_heq _ _ _ _
    (congrArg functorVertex (diagonalFiberTransport_precomp_two p f s.bottom s.right q))
    (congrArg functorVertex (diagonalFiberTransport_precomp_two p f s.left s.top q))
    (congrArg functorVertex (diagonalFiberTransport_precomp p f s.left q)) h hconst

end SerrePositivity.InfinityCategories.F2

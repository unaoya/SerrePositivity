module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareHorizontalPrecomp
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareVerticalPrecomp
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalTwoStepComparisonPrecomp

/-!
概要：任意の実四角形の四辺による指定比較は、元の全係数制限を保つ。
方針：二つの実二辺の自然性を貼り、同じ右上頂点で逆と合成を取る。
規約：四つの元の指定比較を保持。使われ方：元の transportIso の係数自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実四角形の比較値は、全係数を制限しても保持される。 -/
lemma TransportSquareDiagram.comparison_precomp_heq {E B P Q : SSet.{u}}
    {p : E ⟶ B} [LeftFibration p] {a b c d : B _⦋0⦌}
    {s : TransportIntervalSquare P a b c d} {f : P ⟶ vertexFiber p a}
    (D : TransportSquareDiagram p s f) (q : Q ⟶ P) :
    HEq (D.comparison.precomp q) (D.precomp q).comparison := by
  let A := D.rightComparison ≪≫ diagonalFiberTransport_sourceIso p D.bottomComparison s.right
  let C := D.topComparison ≪≫ diagonalFiberTransport_sourceIso p D.leftComparison s.top
  let A' := (D.precomp q).rightComparison ≪≫
    diagonalFiberTransport_sourceIso p (D.precomp q).bottomComparison (q ≫ s.right)
  let C' := (D.precomp q).topComparison ≪≫
    diagonalFiberTransport_sourceIso p (D.precomp q).leftComparison (q ≫ s.top)
  have hA := diagonalTwoStepComparison_precomp_heq p f D.bottomRight D.topRight
    s.bottom s.right D.bottomComparison D.rightComparison q
    (D.precomp q).bottomComparison (D.precomp q).rightComparison
    (D.bottomComparison_precomp_heq q) (D.rightComparison_precomp_heq q)
  have hC := diagonalTwoStepComparison_precomp_heq p f D.topLeft D.topRight
    s.left s.top D.leftComparison D.topComparison q
    (D.precomp q).leftComparison (D.precomp q).topComparison
    (D.leftComparison_precomp_heq q) (D.topComparison_precomp_heq q)
  have hright := congrArg functorVertex
    (diagonalFiberTransport_precomp_two p f s.bottom s.right q)
  have hleft := congrArg functorVertex
    (diagonalFiberTransport_precomp_two p f s.left s.top q)
  have hAsym := vertexIso_symm_heq_of_heq (FunctorIso.precomp A q) A' rfl hright hA
  have hpair := vertexIso_trans_heq_of_heq (FunctorIso.precomp A q).symm (FunctorIso.precomp C q)
    A'.symm C' hright rfl hleft hAsym hC
  simpa only [A, A', C, C', TransportSquareDiagram.comparison,
    TransportIntervalSquare.precomp, functorIso_precomp_trans, functorIso_precomp_symm,
    Iso.trans_assoc] using hpair

end SerrePositivity.InfinityCategories.F2

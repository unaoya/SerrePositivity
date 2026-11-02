module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDiagramComparisonIndependence
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportIntervalUniversalIdentity

/-!
概要：任意の実四角形の四辺比較を、元の選択済み transportIso と同定する。
方針：固定底辺の持ち上げでは下辺比較が恒等となることと、選択独立性を使う。
規約：四つの元の指定比較を保持。使われ方：共通の高次図式から元の面比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {a b c d : B _⦋0⦌}
  {s : TransportIntervalSquare P a b c d} {f : P ⟶ vertexFiber p a}

/-- 固定した元の普遍底辺の指定比較は恒等である。 -/
lemma TransportSquareLift.diagram_bottomComparison (L : TransportSquareLift p s f) :
    L.diagram.bottomComparison = Iso.refl _ := by
  exact (leftFibrationPrism_transportIntervalIso_eq_of_prism_eq p f
    (diagonalFiberTransport p f s.bottom) s.bottom L.diagram.bottomPrism
    (diagonalUniversalPrism p f s.bottom)
    L.diagram.bottomPrism_start (diagonalUniversalPrism_start p f s.bottom)
    L.diagram.bottomPrism_finish (diagonalUniversalPrism_finish p f s.bottom)
    L.diagram.bottomPrism_projection (diagonalUniversalPrism_projection p f s.bottom)
    L.zero).trans (leftFibrationPrism_transportIntervalIso_universal_refl p f s.bottom)

/-- 固定底辺の四辺表示は、元の同じ三辺表示の指定比較に一致する。 -/
lemma TransportSquareLift.diagram_comparison (L : TransportSquareLift p s f) :
    L.diagram.comparison = L.comparison := by
  unfold TransportSquareDiagram.comparison
  rw [L.diagram_bottomComparison, diagonalFiberTransport_sourceIso_refl, Iso.trans_refl]
  rfl

/-- 任意の実底辺を持つ実四角形の比較値は、元の指定 transportIso そのもの。 -/
lemma TransportSquareDiagram.comparison_eq_transportIso (D : TransportSquareDiagram p s f) :
    D.comparison = s.transportIso p f :=
  (D.comparison_eq (transportSquareCanonicalLift p s f).diagram).trans
    (((transportSquareCanonicalLift p s f).diagram_comparison).trans
      (transportSquareCanonicalComparison_eq_transportIso p s f))

end SerrePositivity.InfinityCategories.F2

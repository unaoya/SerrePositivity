module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareDiagramPrecomp
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportIntervalRestrictedComparison

/-!
概要：同じ実四角形の指定した二辺比較は、全係数の制限を保つ。
方針：元の実 prism の制限式と元の区間比較の係数自然性を使う。
規約：元の指定同型を保持。使われ方：指定四角形比較の全係数自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P Q : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {a b c d : B _⦋0⦌}
  {s : TransportIntervalSquare P a b c d} {f : P ⟶ vertexFiber p a}
  (D : TransportSquareDiagram p s f) (q : Q ⟶ P)

/-- 同じ実下辺の指定比較は、任意の全係数制限で値を保つ。 -/
lemma TransportSquareDiagram.bottomComparison_precomp_heq :
    HEq (D.bottomComparison.precomp q) (D.precomp q).bottomComparison := by
  exact leftFibrationPrism_transportIntervalIso_precomp_heq_of_prism p f D.bottomRight
    s.bottom D.bottomPrism D.bottomPrism_start D.bottomPrism_finish D.bottomPrism_projection q
    (D.precomp q).bottomPrism (D.precomp q).bottomPrism_start
    (D.precomp q).bottomPrism_finish (D.precomp q).bottomPrism_projection (by
      dsimp only [TransportSquareDiagram.bottomPrism, TransportSquareDiagram.precomp]
      rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc])

/-- 同じ実上辺の指定比較は、任意の全係数制限で値を保つ。 -/
lemma TransportSquareDiagram.topComparison_precomp_heq :
    HEq (D.topComparison.precomp q) (D.precomp q).topComparison := by
  exact leftFibrationPrism_transportIntervalIso_precomp_heq_of_prism p D.topLeft D.topRight
    s.top D.topPrism D.topPrism_start D.topPrism_finish D.topPrism_projection q
    (D.precomp q).topPrism (D.precomp q).topPrism_start
    (D.precomp q).topPrism_finish (D.precomp q).topPrism_projection (by
      dsimp only [TransportSquareDiagram.topPrism, TransportSquareDiagram.precomp]
      rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc])

end SerrePositivity.InfinityCategories.F2

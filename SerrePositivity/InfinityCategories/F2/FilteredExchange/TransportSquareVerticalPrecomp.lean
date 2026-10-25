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

/-- 同じ実左辺の指定比較は、任意の全係数制限で値を保つ。 -/
lemma TransportSquareDiagram.leftComparison_precomp_heq :
    HEq (D.leftComparison.precomp q) (D.precomp q).leftComparison := by
  exact leftFibrationPrism_transportIntervalIso_precomp_heq_of_prism p f D.topLeft
    s.left D.leftPrism D.leftPrism_start D.leftPrism_finish D.leftPrism_projection q
    (D.precomp q).leftPrism (D.precomp q).leftPrism_start
    (D.precomp q).leftPrism_finish (D.precomp q).leftPrism_projection (by
      dsimp only [TransportSquareDiagram.leftPrism, TransportSquareDiagram.precomp]
      rw [← whiskerLeft_comp_assoc, ← prismEndpoint_naturality, whiskerLeft_comp_assoc])

/-- 同じ実右辺の指定比較は、任意の全係数制限で値を保つ。 -/
lemma TransportSquareDiagram.rightComparison_precomp_heq :
    HEq (D.rightComparison.precomp q) (D.precomp q).rightComparison := by
  exact leftFibrationPrism_transportIntervalIso_precomp_heq_of_prism p D.bottomRight D.topRight
    s.right D.rightPrism D.rightPrism_start D.rightPrism_finish D.rightPrism_projection q
    (D.precomp q).rightPrism (D.precomp q).rightPrism_start
    (D.precomp q).rightPrism_finish (D.precomp q).rightPrism_projection (by
      dsimp only [TransportSquareDiagram.rightPrism, TransportSquareDiagram.precomp]
      rw [← whiskerLeft_comp_assoc, ← prismEndpoint_naturality, whiskerLeft_comp_assoc])

end SerrePositivity.InfinityCategories.F2

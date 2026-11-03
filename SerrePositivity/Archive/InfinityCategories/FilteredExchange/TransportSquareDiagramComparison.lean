module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDiagramVertical

/-!
概要：任意の実底辺を持つ四角形を、四辺の元の指定比較で評価する。
方針：下辺の指定比較を右辺に沿って輸送し、残る三辺と貼り合わせる。
規約：四つの指定同型を保持。使われ方：高次図式の実面を共通の輸送に戻す。
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
  (D : TransportSquareDiagram p s f)

/-- 元の実下辺の指定比較。 -/
def TransportSquareDiagram.bottomComparison :
    FunctorIso D.bottomRight (diagonalFiberTransport p f s.bottom) :=
  leftFibrationPrism_transportIntervalIso p f D.bottomRight s.bottom D.bottomPrism
    D.bottomPrism_start D.bottomPrism_finish D.bottomPrism_projection

/-- 元の実左辺の指定比較。 -/
def TransportSquareDiagram.leftComparison :
    FunctorIso D.topLeft (diagonalFiberTransport p f s.left) :=
  leftFibrationPrism_transportIntervalIso p f D.topLeft s.left D.leftPrism
    D.leftPrism_start D.leftPrism_finish D.leftPrism_projection

/-- 元の実右辺の指定比較。 -/
def TransportSquareDiagram.rightComparison :
    FunctorIso D.topRight (diagonalFiberTransport p D.bottomRight s.right) :=
  leftFibrationPrism_transportIntervalIso p D.bottomRight D.topRight s.right D.rightPrism
    D.rightPrism_start D.rightPrism_finish D.rightPrism_projection

/-- 元の実上辺の指定比較。 -/
def TransportSquareDiagram.topComparison :
    FunctorIso D.topRight (diagonalFiberTransport p D.topLeft s.top) :=
  leftFibrationPrism_transportIntervalIso p D.topLeft D.topRight s.top D.topPrism
    D.topPrism_start D.topPrism_finish D.topPrism_projection

/-- 四つの実辺を同じ元の二段輸送へ戻した比較値。 -/
def TransportSquareDiagram.comparison :
    FunctorIso
      (diagonalFiberTransport p (diagonalFiberTransport p f s.bottom) s.right)
      (diagonalFiberTransport p (diagonalFiberTransport p f s.left) s.top) :=
  (D.rightComparison ≪≫ diagonalFiberTransport_sourceIso p D.bottomComparison s.right).symm ≪≫
    D.topComparison ≪≫ diagonalFiberTransport_sourceIso p D.leftComparison s.top

end SerrePositivity.InfinityCategories.F2

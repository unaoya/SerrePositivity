module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareLiftCorners

/-!
概要：同じ実持ち上げの三辺の指定比較を貼り、元の四角形の合成比較を回収する。
方針：右辺の逆・上辺・左辺比較の輸送像を元の順に合成する。
規約：元の transportIso の選択を保持。使われ方：同じ実四角形による指定合成則の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p]
  {a b c d : B _⦋0⦌} {s : TransportIntervalSquare P a b c d}
  {f : P ⟶ vertexFiber p a} (L : TransportSquareLift p s f)

/-- 元の実左辺の指定比較。 -/
def TransportSquareLift.leftComparison :
    FunctorIso L.topLeft (diagonalFiberTransport p f s.left) :=
  leftFibrationPrism_transportIntervalIso p f L.topLeft s.left L.left
    L.left_start L.left_finish L.left_projection

/-- 元の実右辺の指定比較。 -/
def TransportSquareLift.rightComparison :
    FunctorIso L.topRight (diagonalFiberTransport p
      (diagonalFiberTransport p f s.bottom) s.right) :=
  leftFibrationPrism_transportIntervalIso p (diagonalFiberTransport p f s.bottom)
    L.topRight s.right L.right L.right_start L.right_finish L.right_projection

/-- 元の実上辺の指定比較。 -/
def TransportSquareLift.topComparison :
    FunctorIso L.topRight (diagonalFiberTransport p L.topLeft s.top) :=
  leftFibrationPrism_transportIntervalIso p L.topLeft L.topRight s.top L.top
    L.topLeft_ι.symm L.topRight_ι.symm L.top_projection

/-- 同じ実持ち上げの三辺の指定比較による合成比較。 -/
def TransportSquareLift.comparison :
    FunctorIso
      (diagonalFiberTransport p (diagonalFiberTransport p f s.bottom) s.right)
      (diagonalFiberTransport p (diagonalFiberTransport p f s.left) s.top) :=
  L.rightComparison.symm ≪≫ L.topComparison ≪≫
    diagonalFiberTransport_sourceIso p L.leftComparison s.top

/-- 元の選択済み実四角形による三因子表示は、元の指定 transportIso そのもの。 -/
lemma transportSquareCanonicalComparison_eq_transportIso
    (p : E ⟶ B) [LeftFibration p] (s : TransportIntervalSquare P a b c d)
    (f : P ⟶ vertexFiber p a) :
    (transportSquareCanonicalLift p s f).comparison = s.transportIso p f := by
  rfl

end SerrePositivity.InfinityCategories.F2

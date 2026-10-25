module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTetrahedronSelectedEdges
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTriangleComparisonAlong

/-!
概要：同じ実四面体の四つの元の合成比較を、共通六辺上で表示する。
方針：同じ実共有辺から証明した底の等式だけを使う。
規約：四つの元の指定値を保持。使われ方：指定輸送比較の四面体則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {v : Fin 4 → B _⦋0⦌}
  {f : ∀ i, P ⟶ vertexFiber p (v i)} (D : TransportTetrahedronDiagram p v f)

/-- 元の面 012 の指定比較を、同じ共通三辺で読む。 -/
def TransportTetrahedronDiagram.comparison012 (q : P ⟶ vertexFiber p (v 0)) :
    FunctorIso (diagonalFiberTransport p (diagonalFiberTransport p q D.edge01) D.edge12)
      (diagonalFiberTransport p q D.edge02) :=
  (D.face 3).comparisonAlong q D.edge01 D.edge12 D.edge02
    rfl rfl rfl

/-- 元の面 013 の指定比較を、同じ共通三辺で読む。 -/
def TransportTetrahedronDiagram.comparison013 (q : P ⟶ vertexFiber p (v 0)) :
    FunctorIso (diagonalFiberTransport p (diagonalFiberTransport p q D.edge01) D.edge13)
      (diagonalFiberTransport p q D.edge03) :=
  (D.face 2).comparisonAlong q D.edge01 D.edge13 D.edge03
    D.shared_curve01 rfl D.shared_curve03.symm

/-- 元の面 023 の指定比較を、同じ共通三辺で読む。 -/
def TransportTetrahedronDiagram.comparison023 (q : P ⟶ vertexFiber p (v 0)) :
    FunctorIso (diagonalFiberTransport p (diagonalFiberTransport p q D.edge02) D.edge23)
      (diagonalFiberTransport p q D.edge03) :=
  (D.face 1).comparisonAlong q D.edge02 D.edge23 D.edge03
    D.shared_curve02 rfl rfl

/-- 元の面 123 の指定比較を、同じ共通三辺で読む。 -/
def TransportTetrahedronDiagram.comparison123 (q : P ⟶ vertexFiber p (v 1)) :
    FunctorIso (diagonalFiberTransport p (diagonalFiberTransport p q D.edge12) D.edge23)
      (diagonalFiberTransport p q D.edge13) :=
  (D.face 0).comparisonAlong q D.edge12 D.edge23 D.edge13
    D.shared_curve12 D.shared_curve23 D.shared_curve13

end SerrePositivity.InfinityCategories.F2

module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTetrahedronSharedCurves
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTetrahedronSharedComparisons

/-!
概要：同じ実四面体の六本の元の区間族と選択済み実辺比較を参照する。
方針：各実辺が現れる一つの面から元の値をそのまま取り出す。
規約：選択済みの値を変更しない。使われ方：四面の比較を共通六辺上で計算する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} {v : Fin 4 → B _⦋0⦌}
  {f : ∀ i, P ⟶ vertexFiber p (v i)} (D : TransportTetrahedronDiagram p v f)

/-- 実辺 01 の元の底の族。 -/
def TransportTetrahedronDiagram.edge01 : P ⟶ intervalMappingSpace (v 0) (v 1) :=
  (D.face 3).base.bottom

/-- 実辺 02 の元の底の族。 -/
def TransportTetrahedronDiagram.edge02 : P ⟶ intervalMappingSpace (v 0) (v 2) :=
  (D.face 3).base.left

/-- 実辺 03 の元の底の族。 -/
def TransportTetrahedronDiagram.edge03 : P ⟶ intervalMappingSpace (v 0) (v 3) :=
  (D.face 1).base.left

/-- 実辺 12 の元の底の族。 -/
def TransportTetrahedronDiagram.edge12 : P ⟶ intervalMappingSpace (v 1) (v 2) :=
  (D.face 3).base.right

/-- 実辺 13 の元の底の族。 -/
def TransportTetrahedronDiagram.edge13 : P ⟶ intervalMappingSpace (v 1) (v 3) :=
  (D.face 2).base.right

/-- 実辺 23 の元の底の族。 -/
def TransportTetrahedronDiagram.edge23 : P ⟶ intervalMappingSpace (v 2) (v 3) :=
  (D.face 1).base.right

variable [LeftFibration p]

/-- 実辺 01 の元の選択済み比較。 -/
def TransportTetrahedronDiagram.edgeComparison01 :
    FunctorIso (f 1) (diagonalFiberTransport p (f 0) D.edge01) :=
  (D.face 3).diagram.bottomComparison

/-- 実辺 02 の元の選択済み比較。 -/
def TransportTetrahedronDiagram.edgeComparison02 :
    FunctorIso (f 2) (diagonalFiberTransport p (f 0) D.edge02) :=
  (D.face 3).diagram.leftComparison

/-- 実辺 03 の元の選択済み比較。 -/
def TransportTetrahedronDiagram.edgeComparison03 :
    FunctorIso (f 3) (diagonalFiberTransport p (f 0) D.edge03) :=
  (D.face 1).diagram.leftComparison

/-- 実辺 12 の元の選択済み比較。 -/
def TransportTetrahedronDiagram.edgeComparison12 :
    FunctorIso (f 2) (diagonalFiberTransport p (f 1) D.edge12) :=
  (D.face 3).diagram.rightComparison

/-- 実辺 13 の元の選択済み比較。 -/
def TransportTetrahedronDiagram.edgeComparison13 :
    FunctorIso (f 3) (diagonalFiberTransport p (f 1) D.edge13) :=
  (D.face 2).diagram.rightComparison

/-- 実辺 23 の元の選択済み比較。 -/
def TransportTetrahedronDiagram.edgeComparison23 :
    FunctorIso (f 3) (diagonalFiberTransport p (f 2) D.edge23) :=
  (D.face 1).diagram.rightComparison

end SerrePositivity.InfinityCategories.F2

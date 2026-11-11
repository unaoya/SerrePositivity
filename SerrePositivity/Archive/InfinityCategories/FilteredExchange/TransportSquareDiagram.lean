module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareLiftComparisonIndependence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomPointedShortEdges

/-!
概要：四つの実頂点を指定した、任意の底辺を持つ輸送四角形の持ち上げ。
方針：固定始点と三つの実 fiber 値を、同じ全四角形の四隅で保持する。
規約：底辺を普遍輸送に固定しない。使われ方：高次図式の実面の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全四角形と四つの実 fiber 値を保持する持ち上げ。 -/
structure TransportSquareDiagram {E B P : SSet.{u}} (p : E ⟶ B)
    {a b c d : B _⦋0⦌} (s : TransportIntervalSquare P a b c d)
    (f : P ⟶ vertexFiber p a) where
  /-- 右下の実値。 -/
  bottomRight : P ⟶ vertexFiber p b
  /-- 左上の実値。 -/
  topLeft : P ⟶ vertexFiber p c
  /-- 右上の実値。 -/
  topRight : P ⟶ vertexFiber p d
  /-- 四辺を同時に含む実持ち上げ。 -/
  square : Δ[1] ⊗ (Δ[1] ⊗ P) ⟶ E
  /-- 元の指定四角形を被覆する。 -/
  over_base : square ≫ p = s.square
  /-- 左下角は固定始点。 -/
  origin : (prismEndpoint 0 P ≫ prismEndpoint 0 _) ≫ square = f ≫ vertexFiberι p a
  /-- 右下角は指定実値。 -/
  bottomRight_eq : (prismEndpoint 1 P ≫ prismEndpoint 0 _) ≫ square =
    bottomRight ≫ vertexFiberι p b
  /-- 左上角は指定実値。 -/
  topLeft_eq : (prismEndpoint 0 P ≫ prismEndpoint 1 _) ≫ square =
    topLeft ≫ vertexFiberι p c
  /-- 右上角は指定実値。 -/
  topRight_eq : (prismEndpoint 1 P ≫ prismEndpoint 1 _) ≫ square =
    topRight ≫ vertexFiberι p d

variable {E B P : SSet.{u}} {p : E ⟶ B} {a b c d : B _⦋0⦌}
  {s : TransportIntervalSquare P a b c d} {f : P ⟶ vertexFiber p a}

/-- 元の固定底辺の持ち上げを、同じ実四角形と四隅で読む。 -/
def TransportSquareLift.diagram [LeftFibration p] (L : TransportSquareLift p s f) :
    TransportSquareDiagram p s f where
  bottomRight := diagonalFiberTransport p f s.bottom
  topLeft := L.topLeft
  topRight := L.topRight
  square := L.square
  over_base := L.over_base
  origin := by rw [Category.assoc, L.zero]; exact diagonalUniversalPrism_start p f s.bottom
  bottomRight_eq := by
    rw [Category.assoc, L.zero]; exact diagonalUniversalPrism_finish p f s.bottom
  topLeft_eq := by rw [Category.assoc]; exact L.topLeft_ι.symm
  topRight_eq := by rw [Category.assoc]; exact L.topRight_ι.symm

end SerrePositivity.InfinityCategories.F2

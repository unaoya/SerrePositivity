module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareDiagramChosenComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantFiberPrism

/-!
概要：同じ実三角形を、終辺が実際に定値である持ち上げ四角形で保持する。
方針：元の三つの実 fiber 値と実四角形を一緒に指定する。
規約：任意の底辺を許し、三辺の比較を選び直さない。
使われ方：共通の高次図式の三角形面を元の合成比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 三つの実 fiber 値を持ち、同じ実終辺が定値である三角形の持ち上げ。 -/
structure TransportTriangleDiagram {E B P : SSet.{u}} (p : E ⟶ B)
    {a b d : B _⦋0⦌} (s : TransportIntervalSquare P a b d d)
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b) (h : P ⟶ vertexFiber p d) where
  /-- 同じ実全四角形。 -/
  square : Δ[1] ⊗ (Δ[1] ⊗ P) ⟶ E
  /-- 元の指定四角形を被覆する。 -/
  over_base : square ≫ p = s.square
  /-- 元の実始点。 -/
  origin : (prismEndpoint 0 P ≫ prismEndpoint 0 _) ≫ square = f ≫ vertexFiberι p a
  /-- 元の実中間点。 -/
  middle_eq : (prismEndpoint 1 P ≫ prismEndpoint 0 _) ≫ square = g ≫ vertexFiberι p b
  /-- 元の実終点。 -/
  last_eq : (prismEndpoint 0 P ≫ prismEndpoint 1 _) ≫ square = h ≫ vertexFiberι p d
  /-- 同じ実終辺は、実終点を時間方向で固定した prism そのもの。 -/
  top_constant : prismEndpoint 1 (Δ[1] ⊗ P) ≫ square = constantFiberPrism p h

/-- 同じ実三角形を、上二頂点が同じ実値である実四角形として読む。 -/
def TransportTriangleDiagram.diagram {E B P : SSet.{u}} {p : E ⟶ B}
    {a b d : B _⦋0⦌} {s : TransportIntervalSquare P a b d d}
    {f : P ⟶ vertexFiber p a} {g : P ⟶ vertexFiber p b} {h : P ⟶ vertexFiber p d}
    (T : TransportTriangleDiagram p s f g h) : TransportSquareDiagram p s f where
  bottomRight := g
  topLeft := h
  topRight := h
  square := T.square
  over_base := T.over_base
  origin := T.origin
  bottomRight_eq := T.middle_eq
  topLeft_eq := T.last_eq
  topRight_eq := by
    rw [Category.assoc, T.top_constant, constantFiberPrism_endpoint]

end SerrePositivity.InfinityCategories.F2

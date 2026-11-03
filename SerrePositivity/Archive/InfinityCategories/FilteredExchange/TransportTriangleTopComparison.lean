module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleDiagram
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantIntervalComparison

/-!
概要：実三角形の元の定値終辺比較を、元の定値輸送比較の逆として同定する。
方針：同じ実終辺の厳密な等式と、元の定値 prism 表示を使う。
規約：元の指定比較を保持。使われ方：三辺貼り合わせ式の定値因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} {a b d : B _⦋0⦌}
  {s : TransportIntervalSquare P a b d d} {f : P ⟶ vertexFiber p a}
  {g : P ⟶ vertexFiber p b} {h : P ⟶ vertexFiber p d}
  (T : TransportTriangleDiagram p s f g h)

include T in
/-- 元の実終辺が定値なので、その同じ底の終辺も元の固定終点に定値。 -/
lemma TransportTriangleDiagram.top_base_constant :
    intervalMappingUncurry s.top = SSet.const d := by
  calc
    intervalMappingUncurry s.top = prismEndpoint 1 _ ≫ s.square := s.one.symm
    _ = (prismEndpoint 1 _ ≫ T.square) ≫ p := by rw [Category.assoc, T.over_base]
    _ = SSet.const d := by rw [T.top_constant, constantFiberPrism_projection]

variable [LeftFibration p]

/-- 元の実三角形の終辺比較は、元の同じ定値輸送比較の逆に一致する。 -/
lemma TransportTriangleDiagram.topComparison_eq_constant
    (hs : intervalMappingUncurry s.top = SSet.const d) :
    T.diagram.topComparison = (diagonalFiberTransport_constantIso p h s.top hs).symm := by
  exact leftFibrationPrism_transportIntervalIso_constant_eq p h s.top hs
    T.diagram.topPrism T.diagram.topPrism_start T.diagram.topPrism_finish
    T.diagram.topPrism_projection T.top_constant

end SerrePositivity.InfinityCategories.F2

module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareDiagramHorizontal

/-!
概要：任意の実四角形の左辺・右辺を、同じ実頂点と底の区間で読む。
方針：内側の二端点で制限し、端点交換で同じ四隅へ戻す。
規約：元の全四角形を保持。使われ方：任意の実面の四辺比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} {a b c d : B _⦋0⦌}
  {s : TransportIntervalSquare P a b c d} {f : P ⟶ vertexFiber p a}
  (D : TransportSquareDiagram p s f)

/-- 元の実左辺。 -/
def TransportSquareDiagram.leftPrism := ((Δ[1] : SSet.{u}) ◁ prismEndpoint 0 P) ≫ D.square

/-- 元の実右辺。 -/
def TransportSquareDiagram.rightPrism := ((Δ[1] : SSet.{u}) ◁ prismEndpoint 1 P) ≫ D.square

/-- 左辺は元の left を被覆する。 -/
lemma TransportSquareDiagram.leftPrism_projection :
    D.leftPrism ≫ p = intervalMappingUncurry s.left := by
  rw [TransportSquareDiagram.leftPrism, Category.assoc, D.over_base, s.inner_zero]

/-- 右辺は元の right を被覆する。 -/
lemma TransportSquareDiagram.rightPrism_projection :
    D.rightPrism ≫ p = intervalMappingUncurry s.right := by
  rw [TransportSquareDiagram.rightPrism, Category.assoc, D.over_base, s.inner_one]

/-- 元の左辺の始点。 -/
lemma TransportSquareDiagram.leftPrism_start :
    prismEndpoint 0 P ≫ D.leftPrism = f ≫ vertexFiberι p a := by
  rw [TransportSquareDiagram.leftPrism, ← Category.assoc, prismEndpoint_square_exchange]
  exact D.origin

/-- 元の左辺の終点。 -/
lemma TransportSquareDiagram.leftPrism_finish :
    prismEndpoint 1 P ≫ D.leftPrism = D.topLeft ≫ vertexFiberι p c := by
  rw [TransportSquareDiagram.leftPrism, ← Category.assoc, prismEndpoint_square_exchange]
  exact D.topLeft_eq

/-- 元の右辺の始点。 -/
lemma TransportSquareDiagram.rightPrism_start :
    prismEndpoint 0 P ≫ D.rightPrism = D.bottomRight ≫ vertexFiberι p b := by
  rw [TransportSquareDiagram.rightPrism, ← Category.assoc, prismEndpoint_square_exchange]
  exact D.bottomRight_eq

/-- 元の右辺の終点。 -/
lemma TransportSquareDiagram.rightPrism_finish :
    prismEndpoint 1 P ≫ D.rightPrism = D.topRight ≫ vertexFiberι p d := by
  rw [TransportSquareDiagram.rightPrism, ← Category.assoc, prismEndpoint_square_exchange]
  exact D.topRight_eq

end SerrePositivity.InfinityCategories.F2

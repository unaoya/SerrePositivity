module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDiagram

/-!
概要：任意の実四角形の下辺・上辺を、同じ実頂点と底の区間で読む。
方針：外側の二端点で制限し、四隅と被覆条件を使う。
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

/-- 元の実下辺。 -/
def TransportSquareDiagram.bottomPrism := prismEndpoint 0 _ ≫ D.square

/-- 元の実上辺。 -/
def TransportSquareDiagram.topPrism := prismEndpoint 1 _ ≫ D.square

/-- 下辺は元の bottom を被覆する。 -/
lemma TransportSquareDiagram.bottomPrism_projection :
    D.bottomPrism ≫ p = intervalMappingUncurry s.bottom := by
  rw [TransportSquareDiagram.bottomPrism, Category.assoc, D.over_base, s.zero]

/-- 上辺は元の top を被覆する。 -/
lemma TransportSquareDiagram.topPrism_projection :
    D.topPrism ≫ p = intervalMappingUncurry s.top := by
  rw [TransportSquareDiagram.topPrism, Category.assoc, D.over_base, s.one]

/-- 元の下辺の始点。 -/
lemma TransportSquareDiagram.bottomPrism_start :
    prismEndpoint 0 P ≫ D.bottomPrism = f ≫ vertexFiberι p a :=
  (Category.assoc _ _ _).symm.trans D.origin

/-- 元の下辺の終点。 -/
lemma TransportSquareDiagram.bottomPrism_finish :
    prismEndpoint 1 P ≫ D.bottomPrism = D.bottomRight ≫ vertexFiberι p b :=
  (Category.assoc _ _ _).symm.trans D.bottomRight_eq

/-- 元の上辺の始点。 -/
lemma TransportSquareDiagram.topPrism_start :
    prismEndpoint 0 P ≫ D.topPrism = D.topLeft ≫ vertexFiberι p c :=
  (Category.assoc _ _ _).symm.trans D.topLeft_eq

/-- 元の上辺の終点。 -/
lemma TransportSquareDiagram.topPrism_finish :
    prismEndpoint 1 P ≫ D.topPrism = D.topRight ≫ vertexFiberι p d :=
  (Category.assoc _ _ _).symm.trans D.topRight_eq

end SerrePositivity.InfinityCategories.F2

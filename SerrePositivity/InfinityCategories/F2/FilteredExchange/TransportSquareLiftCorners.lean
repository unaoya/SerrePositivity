module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareLift

/-!
概要：元の持ち上げ四角形の上二頂点を実 fiber 内で保持し、三辺の境界を照合する。
方針：上辺の射影と区間の端点条件で fiber へ持ち上げる。
規約：元の実頂点・三辺を保持。使われ方：元の合成輸送比較の同じ三因子表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p]
  {a b c d : B _⦋0⦌} {s : TransportIntervalSquare P a b c d}
  {f : P ⟶ vertexFiber p a} (L : TransportSquareLift p s f)

/-- 元の全持ち上げの左上頂点。 -/
def TransportSquareLift.topLeft : P ⟶ vertexFiber p c :=
  vertexFiberLift p c (prismEndpoint 0 P ≫ L.top) (by
    rw [Category.assoc, L.top_projection, intervalMappingUncurry_zero])

/-- 元の全持ち上げの右上頂点。 -/
def TransportSquareLift.topRight : P ⟶ vertexFiber p d :=
  vertexFiberLift p d (prismEndpoint 1 P ≫ L.top) (by
    rw [Category.assoc, L.top_projection, intervalMappingUncurry_one])

/-- 左上頂点の包含は同じ実頂点の評価。 -/
lemma TransportSquareLift.topLeft_ι :
    L.topLeft ≫ vertexFiberι p c = prismEndpoint 0 P ≫ L.top := rfl

/-- 右上頂点の包含は同じ実頂点の評価。 -/
lemma TransportSquareLift.topRight_ι :
    L.topRight ≫ vertexFiberι p d = prismEndpoint 1 P ≫ L.top := rfl

private lemma squareEndpoint_exchange (i j : Fin 2) :
    prismEndpoint i P ≫ (Δ[1] ◁ prismEndpoint j P) =
      prismEndpoint j P ≫ prismEndpoint i (Δ[1] ⊗ P) := rfl

/-- 左辺の始点は元の全初期値。 -/
lemma TransportSquareLift.left_start :
    prismEndpoint 0 P ≫ L.left = f ≫ vertexFiberι p a := by
  rw [TransportSquareLift.left, ← Category.assoc, squareEndpoint_exchange,
    Category.assoc, L.zero, diagonalUniversalPrism_start]

/-- 右辺の始点は元の底辺の普遍輸送の終点。 -/
lemma TransportSquareLift.right_start :
    prismEndpoint 0 P ≫ L.right =
      diagonalFiberTransport p f s.bottom ≫ vertexFiberι p b := by
  rw [TransportSquareLift.right, ← Category.assoc, squareEndpoint_exchange,
    Category.assoc, L.zero, diagonalUniversalPrism_finish]

/-- 左辺の終点は元の左上頂点。 -/
lemma TransportSquareLift.left_finish :
    prismEndpoint 1 P ≫ L.left = L.topLeft ≫ vertexFiberι p c := by
  rw [L.topLeft_ι, TransportSquareLift.left, ← Category.assoc, squareEndpoint_exchange,
    Category.assoc, TransportSquareLift.top]

/-- 右辺の終点は元の右上頂点。 -/
lemma TransportSquareLift.right_finish :
    prismEndpoint 1 P ≫ L.right = L.topRight ≫ vertexFiberι p d := by
  rw [L.topRight_ι, TransportSquareLift.right, ← Category.assoc, squareEndpoint_exchange,
    Category.assoc, TransportSquareLift.top]

end SerrePositivity.InfinityCategories.F2

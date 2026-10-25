module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTriangleFromSimplex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SimplexFaceVertexGeometry

/-!
概要：同じ実四面体の任意の面を、三辺を保持する実輸送三角形へ移す。
方針：元の面写像で制限し、実頂点の三つの条件だけを回収する。
規約：四面を独立に充填しない。使われ方：元の合成比較の四面体整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実四面体の任意の三角形面は、元の三頂点と実三辺を保つ輸送図式になる。 -/
def transportTetrahedronFaceOfSimplex {E B P : SSet.{u}} (p : E ⟶ B)
    (W : (Δ[3] : SSet.{u}) ⊗ P ⟶ E) (k : Fin 4) {a b d : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b) (h : P ⟶ vertexFiber p d)
    (h₀ : simplexPrismVertex 3 (k.succAbove 0) P ≫ W = f ≫ vertexFiberι p a)
    (h₁ : simplexPrismVertex 3 (k.succAbove 1) P ≫ W = g ≫ vertexFiberι p b)
    (h₂ : simplexPrismVertex 3 (k.succAbove 2) P ≫ W = h ≫ vertexFiberι p d) :=
  transportTriangleDiagramOfSimplex p ((stdSimplex.δ k ▷ P) ≫ W) f g h
    (by rw [trianglePrism_initial_vertex, ← Category.assoc, simplexPrismVertex_face]; exact h₀)
    (by rw [trianglePrism_middle_vertex, ← Category.assoc, simplexPrismVertex_face]; exact h₁)
    (by rw [trianglePrism_final_vertex, ← Category.assoc, simplexPrismVertex_face]; exact h₂)

end SerrePositivity.InfinityCategories.F2

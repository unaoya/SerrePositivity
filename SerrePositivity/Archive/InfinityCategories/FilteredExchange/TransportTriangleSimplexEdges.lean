module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleFromSimplex

/-!
概要：実二単体から作った輸送三角形の三辺は、元の実面の制限そのもの。
方針：同じ折り畳みの三つの境界式を使う。
規約：元の辺の比較を選び直さない。使われ方：共通四面体の実共有辺の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {E B P : SSet.{u}} (p : E ⟶ B) (W : (Δ[2] : SSet.{u}) ⊗ P ⟶ E)
  {a b d : B _⦋0⦌} (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
  (h : P ⟶ vertexFiber p d)
  (h₀ : (prismEndpoint 0 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ W = f ≫ vertexFiberι p a)
  (h₁ : (prismEndpoint 1 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ W = g ≫ vertexFiberι p b)
  (h₂ : (prismEndpoint 1 P ≫ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫ W = h ≫ vertexFiberι p d)

local notation "T" => transportTriangleDiagramOfSimplex p W f g h h₀ h₁ h₂

/-- 第一辺は同じ実二単体の元の第一辺。 -/
lemma transportTriangleSimplex_bottomPrism :
    TransportSquareDiagram.bottomPrism (TransportTriangleDiagram.diagram T) =
      (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ W := by
  change prismEndpoint 0 _ ≫ (transportTriangleParameter P ≫ W) = _
  rw [← Category.assoc, transportTriangleParameter_bottom]

/-- 長辺は同じ実二単体の元の長辺。 -/
lemma transportTriangleSimplex_leftPrism :
    TransportSquareDiagram.leftPrism (TransportTriangleDiagram.diagram T) =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ W := by
  change ((Δ[1] : SSet.{u}) ◁ prismEndpoint 0 P) ≫
    (transportTriangleParameter P ≫ W) = _
  rw [← Category.assoc, transportTriangleParameter_left]

/-- 最後辺は同じ実二単体の元の最後辺。 -/
lemma transportTriangleSimplex_rightPrism :
    TransportSquareDiagram.rightPrism (TransportTriangleDiagram.diagram T) =
      (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ W := by
  change ((Δ[1] : SSet.{u}) ◁ prismEndpoint 1 P) ≫
    (transportTriangleParameter P ≫ W) = _
  rw [← Category.assoc, transportTriangleParameter_right]

end SerrePositivity.InfinityCategories.F2

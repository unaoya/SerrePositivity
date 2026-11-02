module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleBaseOfLift
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleParameterCorners

/-!
概要：任意の実二単体を、同じ三つの実 fiber 値を持つ三角形図式へ移す。
方針：同じ折り畳みで実全二単体を制限し、三隅と実定値終辺を回収する。
規約：coherent 図式の実面をそのまま保持。使われ方：四面体の全三角形面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の同じ実二単体から、元の三辺と実定値終辺を保持した三角形図式を構成する。 -/
def transportTriangleDiagramOfSimplex {E B P : SSet.{u}} (p : E ⟶ B)
    (W : (Δ[2] : SSet.{u}) ⊗ P ⟶ E) {a b d : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b) (h : P ⟶ vertexFiber p d)
    (h₀ : (prismEndpoint 0 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ W = f ≫ vertexFiberι p a)
    (h₁ : (prismEndpoint 1 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ W = g ≫ vertexFiberι p b)
    (h₂ : (prismEndpoint 1 P ≫ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫ W = h ≫ vertexFiberι p d) :
    TransportTriangleDiagram p (transportTriangleBaseOfLift p W f g h h₀ h₁ h₂) f g h where
  square := transportTriangleParameter P ≫ W
  over_base := by
    change (transportTriangleParameter P ≫ W) ≫ p = transportTriangleParameter P ≫ (W ≫ p)
    exact Category.assoc _ _ _
  origin := by
    rw [← Category.assoc, transportTriangleParameter_bottom_corner]
    exact h₀
  middle_eq := by
    rw [← Category.assoc, transportTriangleParameter_bottom_corner]
    exact h₁
  last_eq := by
    rw [← Category.assoc, transportTriangleParameter_last_corner]
    exact h₂
  top_constant := by
    rw [← Category.assoc, transportTriangleParameter_top_factor, Category.assoc, h₂]
    rfl

end SerrePositivity.InfinityCategories.F2

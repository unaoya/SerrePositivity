module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTriangleBaseSquare
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTriangleDiagram

/-!
概要：実二単体の持ち上げの元の三頂点から、その底の輸送四角形を構成する。
方針：実三頂点の fiber 条件を射影して、同じ実底図式の端点を回収する。
規約：図式の充填や合成則を新しい仮定にしない。使われ方：同じ高次図式の各面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 実二単体の底は、元の実三頂点で指定した三角形の輸送四角形を与える。 -/
def transportTriangleBaseOfLift {E B P : SSet.{u}} (p : E ⟶ B)
    (W : (Δ[2] : SSet.{u}) ⊗ P ⟶ E) {a b d : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b) (h : P ⟶ vertexFiber p d)
    (h₀ : (prismEndpoint 0 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ W = f ≫ vertexFiberι p a)
    (h₁ : (prismEndpoint 1 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫ W = g ≫ vertexFiberι p b)
    (h₂ : (prismEndpoint 1 P ≫ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫ W = h ≫ vertexFiberι p d) :
    TransportIntervalSquare P a b d d := by
  apply transportTriangleBaseSquare (W ≫ p) a b d
  · rw [← Category.assoc, h₀, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  · rw [← Category.assoc, h₁, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  · rw [← Category.assoc, h₂, Category.assoc, vertexFiberι_comp, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2

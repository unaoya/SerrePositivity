module

public import SerrePositivity.InfinityCategories.F2.TriangleFirstEdgeFiberRestrictionEquality
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionFiberWitnessIdentity

/-!
概要：同じ二辺を持つ二つの全三角形の指定長辺比較は恒等同型になる。
方針：第一辺固定の全比較を最後辺へ制限し、同じ実 prism の指定比較を消去する。
規約：元の全二単体・二実辺・実終点を保持。使われ方：全長辺比較の二成分の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全二単体上の二実辺が同じなら、同じ実終点の指定長辺比較は恒等同型。 -/
lemma triangleFixedEdgesLongFiberComparison_eq_refl {A E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (β : (Δ[2] : SSet.{u}) ⊗ A ⟶ B)
    (v : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hv : v ≫ p = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ β)
    (z : B _⦋0⦌)
    (hj : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ β = SSet.const z)
    (W₀ W₁ : (Δ[2] : SSet.{u}) ⊗ A ⟶ E) (h₀ : W₀ ≫ p = β) (h₁ : W₁ ≫ p = β)
    (hi₀ : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ W₀ = v)
    (hi₁ : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ W₁ = v) (g : A ⟶ vertexFiber p z)
    (hj₀ : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ W₀ = g ≫ vertexFiberι p z)
    (hj₁ : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ W₁ = g ≫ vertexFiberι p z)
    (he : (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ W₀ = (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ W₁) :
    triangleFirstEdgeLongFiberComparison p β v hv z hj W₀ W₁ h₀ h₁ hi₀ hi₁ g g hj₀ hj₁ =
      Iso.refl _ := by
  rw [triangleFirstEdgeLongFiberComparison_eq_last]
  unfold triangleFirstEdgeLastFiberComparison
  exact relativeExtensionFiberEndpoint_witnessIso_eq_refl_of_eq p _ _
    (prismEndpoint_zero_leftAnodyne A) _ _ _ z _ _ _ _ _ _ _ g _ _ he

end SerrePositivity.InfinityCategories.F2

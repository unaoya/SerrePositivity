module

public import SerrePositivity.InfinityCategories.F2.TriangleFirstEdgeFiberComparison

/-!
概要：同じ最初辺を共有する二つの全三角形の長辺と最後辺の実 fiber 比較を保持する。
方針：元の二面への実制限を、対応する始点固定の全 prism 空間で比較する。
規約：両実 prism と実終点を保持。使われ方：長辺輸送と最後辺輸送の指定値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (β : (Δ[2] : SSet.{u}) ⊗ A ⟶ B) (v : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
  (hv : v ≫ p = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ β)
local notation "i" => stdSimplex.δ (2 : Fin 3) ▷ A
local notation "j" => prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)
local notation "L" => stdSimplex.δ (1 : Fin 3) ▷ A
local notation "R" => stdSimplex.δ (0 : Fin 3) ▷ A
variable (z : B _⦋0⦌) (hj : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ β = SSet.const z)
  (W₀ W₁ : (Δ[2] : SSet.{u}) ⊗ A ⟶ E) (h₀ : W₀ ≫ p = β) (h₁ : W₁ ≫ p = β)
  (hi₀ : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ W₀ = v) (hi₁ : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ W₁ = v)
  (g₀ g₁ : A ⟶ vertexFiber p z)
  (hj₀ : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ W₀ = g₀ ≫ vertexFiberι p z)
  (hj₁ : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ W₁ = g₁ ≫ vertexFiberι p z)

/-- 同じ長辺の二実 prism の、元の始点と終点を保つ指定 fiber 比較。 -/
def triangleFirstEdgeLongFiberComparison : FunctorIso g₀ g₁ :=
  relativeExtensionFiberEndpoint_witnessIso p (L ≫ β) (prismEndpoint 0 A)
    (prismEndpoint_zero_leftAnodyne A) (prismEndpoint 0 A ≫ v)
    (by rw [Category.assoc, hv, ← Category.assoc,
      ← triangleFirstEdge_long_initial_square, Category.assoc])
    (prismEndpoint 1 A) z (by simpa only [Category.assoc] using hj)
    (L ≫ W₀) (L ≫ W₁) (by rw [Category.assoc, h₀]) (by rw [Category.assoc, h₁])
    (by rw [← Category.assoc, triangleFirstEdge_long_initial_square, Category.assoc, hi₀])
    (by rw [← Category.assoc, triangleFirstEdge_long_initial_square, Category.assoc, hi₁])
    g₀ g₁ (by simpa only [Category.assoc] using hj₀)
      (by simpa only [Category.assoc] using hj₁)

/-- 同じ最後辺の二実 prism の、元の中間点と終点を保つ指定 fiber 比較。 -/
def triangleFirstEdgeLastFiberComparison : FunctorIso g₀ g₁ :=
  relativeExtensionFiberEndpoint_witnessIso p (R ≫ β) (prismEndpoint 0 A)
    (prismEndpoint_zero_leftAnodyne A) (prismEndpoint 1 A ≫ v)
    (by rw [Category.assoc, hv, ← Category.assoc,
      ← triangleFirstEdge_last_initial_square, Category.assoc])
    (prismEndpoint 1 A) z (by
      rw [← Category.assoc, triangleFirstEdge_last_final_square]
      exact hj)
    (R ≫ W₀) (R ≫ W₁) (by rw [Category.assoc, h₀]) (by rw [Category.assoc, h₁])
    (by rw [← Category.assoc, triangleFirstEdge_last_initial_square, Category.assoc, hi₀])
    (by rw [← Category.assoc, triangleFirstEdge_last_initial_square, Category.assoc, hi₁])
    g₀ g₁ (by rw [← Category.assoc, triangleFirstEdge_last_final_square]; exact hj₀)
      (by rw [← Category.assoc, triangleFirstEdge_last_final_square]; exact hj₁)

end SerrePositivity.InfinityCategories.F2

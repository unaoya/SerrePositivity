module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TriangleFirstEdgeFiberRestriction

/-!
概要：同じ最初辺を固定した全三角形の指定比較は、長辺と最後辺で同じ値を与える。
方針：同じ実終点を保つ制限に指定 fiber 比較の厳密な自然性を適用する。
規約：元の二つの全持ち上げを保持。使われ方：長辺比較を元の最後辺輸送比較へ戻す。
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
variable (z : B _⦋0⦌) (hj : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ β = SSet.const z)
  (W₀ W₁ : (Δ[2] : SSet.{u}) ⊗ A ⟶ E) (h₀ : W₀ ≫ p = β) (h₁ : W₁ ≫ p = β)
  (hi₀ : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ W₀ = v) (hi₁ : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ W₁ = v)
  (g₀ g₁ : A ⟶ vertexFiber p z)
  (hj₀ : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ W₀ = g₀ ≫ vertexFiberι p z)
  (hj₁ : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ W₁ = g₁ ≫ vertexFiberι p z)

/-- 元の全比較を長辺へ制限しても、同じ二つの長辺 prism の指定値を厳密に回収する。 -/
lemma triangleFirstEdgeFiberComparison_eq_long :
    triangleFirstEdgeFiberComparison p β v hv z hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁ =
    triangleFirstEdgeLongFiberComparison p β v hv z hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁ := by
  exact relativeExtensionFiberEndpoint_witnessIso_restriction p β i
    (triangleFirstEdge_prism_leftAnodyne A) v hv
    (stdSimplex.δ (1 : Fin 3) ▷ A) (prismEndpoint 0 A) (prismEndpoint 0 A)
    (prismEndpoint_zero_leftAnodyne A) (triangleFirstEdge_long_initial_square A)
    j (prismEndpoint 1 A) rfl z hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁

/-- 元の全比較を最後辺へ制限しても、同じ二つの最後辺 prism の指定値を厳密に回収する。 -/
lemma triangleFirstEdgeFiberComparison_eq_last :
    triangleFirstEdgeFiberComparison p β v hv z hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁ =
    triangleFirstEdgeLastFiberComparison p β v hv z hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁ := by
  exact relativeExtensionFiberEndpoint_witnessIso_restriction p β i
    (triangleFirstEdge_prism_leftAnodyne A) v hv
    (stdSimplex.δ (0 : Fin 3) ▷ A) (prismEndpoint 1 A) (prismEndpoint 0 A)
    (prismEndpoint_zero_leftAnodyne A) (triangleFirstEdge_last_initial_square A)
    j (prismEndpoint 1 A) (triangleFirstEdge_last_final_square A) z hj
    W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁

/-- 元の最初辺が同じなら、長辺と最後辺の二つの指定終点比較は全係数で厳密に一致する。 -/
lemma triangleFirstEdgeLongFiberComparison_eq_last :
    triangleFirstEdgeLongFiberComparison p β v hv z hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁ =
    triangleFirstEdgeLastFiberComparison p β v hv z hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁ :=
  (triangleFirstEdgeFiberComparison_eq_long p β v hv z hj
    W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁).symm.trans
      (triangleFirstEdgeFiberComparison_eq_last p β v hv z hj
        W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁)

end SerrePositivity.InfinityCategories.F2

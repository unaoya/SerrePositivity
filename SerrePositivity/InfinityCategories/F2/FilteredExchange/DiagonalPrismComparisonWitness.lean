module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalUniversalPrism

/-!
概要：元の全対角輸送の指定比較を、同じ二実 prism の fiber 終点比較へ厳密に戻す。
方針：元の普遍 prism を実データとして表示し、元の定義とそのまま照合する。
規約：元の指定同型を保持。使われ方：同じ係数制限で元の長辺比較へ値を移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {P E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (f : P ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ P ⟶ B)
  (h₀ : prismEndpoint 0 P ≫ γ = SSet.const a)
include h₀

/-- 元の動く初期値は、元の同じ底の初点を被覆する。 -/
lemma diagonalPrismComparison_initial_base :
    (f ≫ vertexFiberι p a) ≫ p = prismEndpoint 0 P ≫ γ := by
  rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, h₀]

/-- 元の全対角の指定比較は、元の同じ二実 prism の fiber 終点比較そのもの。 -/
lemma leftFibrationPrism_diagonalTransportIso_eq_witness
    (g : P ⟶ vertexFiber p b) (h₁ : prismEndpoint 1 P ≫ γ = SSet.const b)
    (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)
    (H₀ : prismEndpoint 0 P ≫ H = f ≫ vertexFiberι p a)
    (H₁ : prismEndpoint 1 P ≫ H = g ≫ vertexFiberι p b) (Hp : H ≫ p = γ) :
    leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ H H₀ H₁ Hp =
    relativeExtensionFiberEndpoint_witnessIso p γ (prismEndpoint 0 P)
      (prismEndpoint_zero_leftAnodyne P) (f ≫ vertexFiberι p a)
      (diagonalPrismComparison_initial_base p f γ h₀) (prismEndpoint 1 P) b h₁
      H (diagonalUniversalPrism p f (intervalMappingCurryOfEndpoints γ h₀ h₁)) Hp
      (by
        rw [diagonalUniversalPrism_projection]
        exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁)
      H₀ (diagonalUniversalPrism_start p f (intervalMappingCurryOfEndpoints γ h₀ h₁))
      g (diagonalFiberTransport p f (intervalMappingCurryOfEndpoints γ h₀ h₁)) H₁
      (diagonalUniversalPrism_finish p f (intervalMappingCurryOfEndpoints γ h₀ h₁)) := rfl

end SerrePositivity.InfinityCategories.F2

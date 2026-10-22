module

public import SerrePositivity.InfinityCategories.F2.DiagonalPrismComparisonWitness
public import SerrePositivity.InfinityCategories.F2.PrismFiberWitnessReindex

/-!
概要：元の全対角比較の同じ係数制限を、元の二実 prism の制限の比較へ厳密に戻す。
方針：指定比較の実二 prism 表示と、既存の fiber 比較の制限則を適用する。
規約：元の比較・両 prism・実両端を保持。使われ方：元の長辺比較との値照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全対角輸送の同じ係数制限は、同じ二実 prism の制限の指定 fiber 比較。 -/
lemma leftFibrationPrism_diagonalTransportIso_precomp_eq_witness {P Q E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
    (γ : (Δ[1] : SSet.{u}) ⊗ P ⟶ B)
    (h₀ : prismEndpoint 0 P ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 P ≫ γ = SSet.const b)
    (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)
    (H₀ : prismEndpoint 0 P ≫ H = f ≫ vertexFiberι p a)
    (H₁ : prismEndpoint 1 P ≫ H = g ≫ vertexFiberι p b) (Hp : H ≫ p = γ) (r : Q ⟶ P) :
    (leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ H H₀ H₁ Hp).precomp r =
    relativeExtensionFiberEndpoint_witnessIso p ((Δ[1] ◁ r) ≫ γ) (prismEndpoint 0 Q)
      (prismEndpoint_zero_leftAnodyne Q) (r ≫ f ≫ vertexFiberι p a)
      (by
        rw [Category.assoc, diagonalPrismComparison_initial_base p f γ h₀,
          ← Category.assoc, ← prismEndpoint_naturality, Category.assoc])
      (prismEndpoint 1 Q) b (by
        rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₁, SSet.comp_const])
      ((Δ[1] ◁ r) ≫ H)
      ((Δ[1] ◁ r) ≫ diagonalUniversalPrism p f (intervalMappingCurryOfEndpoints γ h₀ h₁))
      (by rw [Category.assoc, Hp])
      (by
        rw [Category.assoc, diagonalUniversalPrism_projection,
          intervalMappingUncurry_curryOfEndpoints])
      (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, H₀])
      (by
        rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
          diagonalUniversalPrism_start])
      (r ≫ g) (r ≫ diagonalFiberTransport p f (intervalMappingCurryOfEndpoints γ h₀ h₁))
      (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, H₁, Category.assoc])
      (by
        rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
          diagonalUniversalPrism_finish, Category.assoc]) := by
  rw [leftFibrationPrism_diagonalTransportIso_eq_witness p f γ h₀ g h₁ H H₀ H₁ Hp]
  exact prismFiberWitnessIso_precomp p γ (f ≫ vertexFiberι p a)
    (diagonalPrismComparison_initial_base p f γ h₀) b h₁ H
    (diagonalUniversalPrism p f (intervalMappingCurryOfEndpoints γ h₀ h₁)) Hp
    (by
      rw [diagonalUniversalPrism_projection]
      exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁)
    H₀ (diagonalUniversalPrism_start p f (intervalMappingCurryOfEndpoints γ h₀ h₁)) g
    (diagonalFiberTransport p f (intervalMappingCurryOfEndpoints γ h₀ h₁)) H₁
    (diagonalUniversalPrism_finish p f (intervalMappingCurryOfEndpoints γ h₀ h₁)) r

end SerrePositivity.InfinityCategories.F2

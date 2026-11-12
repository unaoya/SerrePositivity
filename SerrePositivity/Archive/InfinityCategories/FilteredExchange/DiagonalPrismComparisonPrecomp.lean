module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismRestrictedWitness
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointDataEquality
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomCosliceKanAction

/-!
概要：元の対角比較の全係数制限を、同じ制限後の実 prism の元の対角比較へ戻す。
方針：元の二実 prism の制限式と、普遍対角 prism の制限式を使う。
規約：指定比較の値を保持。使われ方：固定射の全値比較と元の実長辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全対角比較の制限は、同じ元の初期値・実 prism の制限による対角比較。 -/
lemma leftFibrationPrism_diagonalTransportIso_precomp_heq {E B K L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : K ⟶ vertexFiber p a) (g : K ⟶ vertexFiber p b)
    (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (h₀ : prismEndpoint 0 K ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 K ≫ γ = SSet.const b)
    (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (hs : prismEndpoint 0 K ≫ H = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 K ≫ H = g ≫ vertexFiberι p b) (hp : H ≫ p = γ) (r : L ⟶ K)
    (h₀' : prismEndpoint 0 L ≫ ((Δ[1] ◁ r) ≫ γ) = SSet.const a)
    (h₁' : prismEndpoint 1 L ≫ ((Δ[1] ◁ r) ≫ γ) = SSet.const b) :
    HEq ((leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ H hs he hp).precomp r)
      (leftFibrationPrism_diagonalTransportIso p (r ≫ f) (r ≫ g) ((Δ[1] ◁ r) ≫ γ)
        h₀' h₁' ((Δ[1] ◁ r) ≫ H)
        (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hs, Category.assoc])
        (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, he, Category.assoc])
        (by rw [Category.assoc, hp])) := by
  rw [leftFibrationPrism_diagonalTransportIso_precomp_eq_witness,
    leftFibrationPrism_diagonalTransportIso_eq_witness]
  have hc : intervalMappingCurryOfEndpoints ((Δ[1] ◁ r) ≫ γ) h₀' h₁' =
      r ≫ intervalMappingCurryOfEndpoints γ h₀ h₁ := by
    apply intervalMappingUncurry_injective
    rw [intervalMappingUncurry_curryOfEndpoints, intervalMappingUncurry_precomp,
      intervalMappingUncurry_curryOfEndpoints]
  apply relativeExtensionFiberEndpoint_witnessIso_heq_of_dataEq
  · rfl
  · exact (Category.assoc _ _ _).symm
  · rfl
  · rw [diagonalUniversalPrism_precomp, hc]
  · rfl
  · rw [diagonalFiberTransport_precomp, hc]

end SerrePositivity.InfinityCategories.F2

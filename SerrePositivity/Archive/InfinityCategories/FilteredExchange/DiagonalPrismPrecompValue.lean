module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismComparisonPrecomp
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：元の対角比較の値の係数制限を、同じ制限後の実 prism の指定比較の値へ戻す。
方針：前後合成の交換と元の指定対角比較の制限則を使う。
規約：元の指定値・全係数を保持。使われ方：固定射値比較と元の実長辺の値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定対角比較の値の制限は、同じ実 prism の制限後の指定比較の値と一致。 -/
lemma leftFibrationPrism_diagonalTransportIso_precomp_postcomp_heq {E B K L Z : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : K ⟶ vertexFiber p a) (g : K ⟶ vertexFiber p b)
    (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (h₀ : prismEndpoint 0 K ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 K ≫ γ = SSet.const b)
    (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (hs : prismEndpoint 0 K ≫ H = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 K ≫ H = g ≫ vertexFiberι p b) (hp : H ≫ p = γ) (r : L ⟶ K)
    (h₀' : prismEndpoint 0 L ≫ ((Δ[1] ◁ r) ≫ γ) = SSet.const a)
    (h₁' : prismEndpoint 1 L ≫ ((Δ[1] ◁ r) ≫ γ) = SSet.const b)
    (V : vertexFiber p b ⟶ Z) :
    HEq (FunctorIso.precomp
        ((leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ H hs he hp).postcomp V) r)
      ((leftFibrationPrism_diagonalTransportIso p (r ≫ f) (r ≫ g) ((Δ[1] ◁ r) ≫ γ)
        h₀' h₁' ((Δ[1] ◁ r) ≫ H)
        (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hs, Category.assoc])
        (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, he, Category.assoc])
        (by rw [Category.assoc, hp])).postcomp V) := by
  let e := leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ H hs he hp
  let e' := leftFibrationPrism_diagonalTransportIso p (r ≫ f) (r ≫ g) ((Δ[1] ◁ r) ≫ γ)
    h₀' h₁' ((Δ[1] ◁ r) ≫ H)
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hs, Category.assoc])
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, he, Category.assoc])
    (by rw [Category.assoc, hp])
  have hc : intervalMappingCurryOfEndpoints ((Δ[1] ◁ r) ≫ γ) h₀' h₁' =
      r ≫ intervalMappingCurryOfEndpoints γ h₀ h₁ := by
    apply intervalMappingUncurry_injective
    rw [intervalMappingUncurry_curryOfEndpoints, intervalMappingUncurry_precomp,
      intervalMappingUncurry_curryOfEndpoints]
  have ht : r ≫ diagonalFiberTransport p f (intervalMappingCurryOfEndpoints γ h₀ h₁) =
      diagonalFiberTransport p (r ≫ f)
        (intervalMappingCurryOfEndpoints ((Δ[1] ◁ r) ≫ γ) h₀' h₁') := by
    rw [diagonalFiberTransport_precomp, hc]
  have h := leftFibrationPrism_diagonalTransportIso_precomp_heq
    p f g γ h₀ h₁ H hs he hp r h₀' h₁'
  exact (heq_of_eq (functorIso_precomp_postcomp e r V).symm).trans
    (functorIso_postcomp_heq_of_heq e' (e.precomp r) rfl ht.symm h V)

end SerrePositivity.InfinityCategories.F2

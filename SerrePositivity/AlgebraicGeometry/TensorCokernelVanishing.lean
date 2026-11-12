module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import SerrePositivity.AlgebraicGeometry.SupportFromLocalizedTensor

/-!
概要：線形写像のテンソル化が全射なら、余核のテンソル積は零。
方針：テンソル積の右完全性を実際の余核の商写像へ適用する。
規約：平坦性はこの代数的な段には不要。
使われ方：切断部分代数の次数零の余核の台を局所化で判定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open TensorProduct
open scoped TensorProduct
universe u
variable {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] (φ : M →ₗ[R] N)

/-- 写像のテンソル化が全射なら、実際の余核のテンソル積は零。 -/
theorem tensorCokernel_subsingleton_of_surjective
    (Q : Type u) [AddCommGroup Q] [Module R Q]
    (hφ : Function.Surjective (φ.lTensor Q)) :
    Subsingleton (Q ⊗[R] (N ⧸ LinearMap.range φ)) := by
  let π := (LinearMap.range φ).mkQ
  have hex : Function.Exact φ π := by
    rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ (LinearMap.range φ)
  have ht := lTensor_exact Q hex (Submodule.mkQ_surjective (LinearMap.range φ))
  have hz (x : Q ⊗[R] (N ⧸ LinearMap.range φ)) : x = 0 := by
    obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective Q
      (Submodule.mkQ_surjective (LinearMap.range φ)) x
    obtain ⟨z, hz⟩ := hφ y
    exact hy.symm.trans ((ht y).mpr ⟨z, hz⟩)
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

/-- 中心外の局所化テンソル積で写像が全射なら、その余核の台は中心内。 -/
theorem cokernel_support_subset_of_localizedTensor_surjective (I : Ideal R)
    (h : ∀ P : PrimeSpectrum R, P ∉ PrimeSpectrum.zeroLocus (I : Set R) →
      Function.Surjective (φ.lTensor (Localization P.asIdeal.primeCompl))) :
    Module.support R (N ⧸ LinearMap.range φ) ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  apply support_subset_of_localizedTensor_subsingleton
  intro P hP
  exact tensorCokernel_subsingleton_of_surjective φ _ (h P hP)

end SerrePositivity.AlgebraicGeometry

module
public import SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitImage
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Hom複体の短完全列の比較に用いる中央項の五項補題 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex ComposableArrows

lemma complexQuasiIso_middle_of_shortExact {A : Type u} [CommRing A]
    {S₁ S₂ : ShortComplex (Complex A)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  have := h₁
  have := h₃
  constructor
  intro q
  apply (quasiIsoAt_iff_isIso_homologyMap _ q).2
  have hp : (ComplexShape.up ℤ).Rel (q - 1) q := ComplexShape.up_mk _ _ (by omega)
  have hn : (ComplexShape.up ℤ).Rel q (q + 1) := ComplexShape.up_mk _ _ rfl
  let R₁ := mk₄ (hS₁.δ (q - 1) q hp) (homologyMap S₁.f q)
    (homologyMap S₁.g q) (hS₁.δ q (q + 1) hn)
  let R₂ := mk₄ (hS₂.δ (q - 1) q hp) (homologyMap S₂.f q)
    (homologyMap S₂.g q) (hS₂.δ q (q + 1) hn)
  have he₁ : R₁.Exact := exact_of_δ₀
    (hS₁.homology_exact₁ (q - 1) q hp).exact_toComposableArrows
    (exact_of_δ₀ (hS₁.homology_exact₂ q).exact_toComposableArrows
      (hS₁.homology_exact₃ q (q + 1) hn).exact_toComposableArrows)
  have he₂ : R₂.Exact := exact_of_δ₀
    (hS₂.homology_exact₁ (q - 1) q hp).exact_toComposableArrows
    (exact_of_δ₀ (hS₂.homology_exact₂ q).exact_toComposableArrows
      (hS₂.homology_exact₃ q (q + 1) hn).exact_toComposableArrows)
  let ψ : R₁ ⟶ R₂ := homMk₄ (homologyMap φ.τ₃ (q - 1)) (homologyMap φ.τ₁ q)
    (homologyMap φ.τ₂ q) (homologyMap φ.τ₃ q) (homologyMap φ.τ₁ (q + 1))
    (HomologySequence.δ_naturality φ hS₁ hS₂ (q - 1) q hp)
    (by
      dsimp [R₁, R₂]
      rw [← homologyMap_comp, ← homologyMap_comp, φ.comm₁₂])
    (by
      dsimp [R₁, R₂]
      rw [← homologyMap_comp, ← homologyMap_comp, φ.comm₂₃])
    (HomologySequence.δ_naturality φ hS₁ hS₂ q (q + 1) hn)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono he₁ he₂ ψ
    (by dsimp [ψ]; infer_instance) (by dsimp [ψ]; infer_instance)
    (by dsimp [ψ]; infer_instance) (by dsimp [ψ]; infer_instance)

end SerrePositivity.DifferentialGraded

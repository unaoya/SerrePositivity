module

public import SerrePositivity.HomologicalAlgebra.CochainIdempotentQuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Short exact sequences of idempotent images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
  (e₁ : CochainIdempotent S.X₁) (e₂ : CochainIdempotent S.X₂) (e₃ : CochainIdempotent S.X₃)
  (hf : e₁.map ≫ S.f = S.f ≫ e₂.map) (hg : e₂.map ≫ S.g = S.g ≫ e₃.map)

/-- A short complex restricts to compatible idempotent images. -/
def imageShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (imageMap e₁ e₂ S.f hf) (imageMap e₂ e₃ S.g hg) (by
    apply (cancel_mono e₃.inclusion).1
    simp only [Category.assoc, imageMap_inclusion, imageMap_inclusion_assoc, S.zero,
      comp_zero, zero_comp])

/-- The restricted short complex is a retract of the original one. -/
def imageShortComplexRetract : Retract (imageShortComplex S e₁ e₂ e₃ hf hg) S where
  i := {
    τ₁ := e₁.inclusion
    τ₂ := e₂.inclusion
    τ₃ := e₃.inclusion
    comm₁₂ := (imageMap_inclusion e₁ e₂ S.f hf).symm
    comm₂₃ := (imageMap_inclusion e₂ e₃ S.g hg).symm }
  r := {
    τ₁ := e₁.projection
    τ₂ := e₂.projection
    τ₃ := e₃.projection
    comm₁₂ := projection_imageMap e₁ e₂ S.f hf
    comm₂₃ := projection_imageMap e₂ e₃ S.g hg }
  retract := by
    apply ShortComplex.hom_ext <;> simp [imageShortComplex]

/-- Exactness is preserved by restriction to compatible idempotent images. -/
lemma imageShortComplex_exact (hS : S.Exact) : (imageShortComplex S e₁ e₂ e₃ hf hg).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  have h := (imageShortComplexRetract S e₁ e₂ e₃ hf hg).map
    (ShortComplex.homologyFunctor (CochainComplex (ModuleCat.{u} R) ℤ))
  change IsZero ((ShortComplex.homologyFunctor
    (CochainComplex (ModuleCat.{u} R) ℤ)).obj (imageShortComplex S e₁ e₂ e₃ hf hg))
  rw [IsZero.iff_id_eq_zero, ← h.retract]
  have hz : IsZero ((ShortComplex.homologyFunctor
    (CochainComplex (ModuleCat.{u} R) ℤ)).obj S) :=
    (ShortComplex.exact_iff_isZero_homology S).mp hS
  rw [hz.eq_of_tgt h.i 0, zero_comp]

/-- Short exactness is preserved by restriction to compatible idempotent images. -/
lemma imageShortComplex_shortExact (hS : S.ShortExact) :
    (imageShortComplex S e₁ e₂ e₃ hf hg).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact {
    mono_f := (MorphismProperty.monomorphisms _).of_retract
      (imageMapRetract e₁ e₂ S.f hf) inferInstance
    epi_g := (MorphismProperty.epimorphisms _).of_retract
      (imageMapRetract e₂ e₃ S.g hg) inferInstance
    exact := imageShortComplex_exact S e₁ e₂ e₃ hf hg hS.exact }

end CochainIdempotent
end SerrePositivity

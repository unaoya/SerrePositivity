module
public import SerrePositivity.PerfectComplex.ClosedSupportRelations

/-! # Descending evaluations from concrete cone relations to supported K₀ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits Pretriangulated
variable {R : Type u} [CommRing R]
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) {B : Type*} [AddCommGroup B]

/-- It suffices to verify a supported additive evaluation on concrete mapping cones. -/
lemma closedSupport_triangleAdditive_of_cone
    (χ : SupportedPerfectHomotopyOn Z → B)
    (hi : ∀ {X Y : SupportedPerfectHomotopyOn Z}, (X ≅ Y) → χ X = χ Y)
    (hc : ∀ (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
      (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
      (sp : HasHomologySupportOn Z P) (sq : HasHomologySupportOn Z Q) (f : P ⟶ Q),
      χ (supportedPerfectOnObj Z (CochainComplex.mappingCone f)
        (strictlyPerfectComplex_mappingCone R f hp hq) (sp.mappingCone f sq)) =
        χ (supportedPerfectOnObj Z Q hq sq) - χ (supportedPerfectOnObj Z P hp sp)) :
    ∀ (T : Triangle (SupportedPerfectHomotopyOn Z)), T ∈ distTriang _ →
      χ T.obj₂ = χ T.obj₁ + χ T.obj₃ := by
  have hshort : ClosedSupportShortExactAdditive Z χ := by
    intro S hS h₁ h₂ h₃ s₁ s₂ s₃
    have hqiso := CochainComplex.mappingCone.quasiIso_descShortComplex hS
    obtain ⟨e, _⟩ := (strictlyPerfectComplex_quasiIso_iff
      (strictlyPerfectComplex_mappingCone R S.f h₁ h₂) h₃
      (CochainComplex.mappingCone.descShortComplex S)).mp hqiso
    have he := hi (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (HomotopyCategory.isoOfHomotopyEquiv e)) :
      supportedPerfectOnObj Z (CochainComplex.mappingCone S.f)
        (strictlyPerfectComplex_mappingCone R S.f h₁ h₂) (s₁.mappingCone S.f s₂) ≅
      supportedPerfectOnObj Z S.X₃ h₃ s₃)
    rw [← he, hc S.X₁ S.X₂ h₁ h₂ s₁ s₂ S.f]
    abel
  exact hshort.triangle hi
end SerrePositivity

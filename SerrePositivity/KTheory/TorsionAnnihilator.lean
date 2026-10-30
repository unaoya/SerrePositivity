module
public import SerrePositivity.KTheory.G0Torsion
public import SerrePositivity.CommutativeAlgebra.Support.Closed

/-! # Principal support for a finite localization-torsion module -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R] {P : Submonoid R}

/-- A supported torsion module has a uniformly smaller closed support. -/
lemma exists_annihilator_supportedOn
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (M : SupportedFGModuleOn Z)
    (h : Module.IsTorsion' M.obj P) :
    ∃ r ∈ P, finiteModuleSupportedOn
      (Z ⊓ supportZeroLocus (Ideal.span ({r} : Set R))) M.obj := by
  obtain ⟨r, hr, er⟩ := exists_annihilating_mem_of_isTorsion' h
  exact ⟨r, hr, M.property.1, fun p hp =>
    ⟨M.property.2 hp, module_support_subset_zeroLocus_of_annihilator r er hp⟩⟩
end SerrePositivity

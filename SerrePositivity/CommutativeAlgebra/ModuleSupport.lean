module
public import SerrePositivity.CommutativeAlgebra.ClosedSupportGeometry
public import SerrePositivity.CommutativeAlgebra.LocalizationTorsion
public import Mathlib.RingTheory.Support

/-! # Support bounds from exactness and annihilators -/
@[expose] public section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- Exactness alone bounds the middle support by the union of the two outer supports. -/
lemma module_support_subset_union_of_exact
    {M N L : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
    [Module R M] [Module R N] [Module R L]
    (f : M →ₗ[R] N) (g : N →ₗ[R] L) (h : Function.Exact f g) :
    Module.support R N ⊆ Module.support R M ∪ Module.support R L := by
  intro p
  contrapose
  simp only [Set.mem_union, not_or, and_imp, Module.notMem_support_iff']
  intro hM hL
  exact IsModuleSTorsion.of_exact (P := p.asIdeal.primeCompl) f g h hM hL

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- An annihilator puts the support in its principal vanishing locus. -/
lemma module_support_subset_zeroLocus_of_annihilator (r : R) (h : ∀ m : M, r • m = 0) :
    Module.support R M ⊆ supportZeroLocus (Ideal.span ({r} : Set R)) := by
  intro p hp
  apply Ideal.span_le.mpr
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  exact Module.annihilator_le_of_mem_support hp (Module.mem_annihilator.mpr h)

end SerrePositivity

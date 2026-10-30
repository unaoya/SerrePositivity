module
public import SerrePositivity.CommutativeAlgebra.ModuleSupport
public import Mathlib.RingTheory.Support
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.SupportDimension

/-! # The closed support of a finite module -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open IsLocalRing TensorProduct
variable (R : Type u) [CommRing R]

/-- Support of a finite module, represented as the zero locus of its annihilator. -/
def finiteModuleClosedSupport (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    TopologicalSpace.Closeds (PrimeSpectrum R) := supportZeroLocus (Module.annihilator R M)

@[simp]
lemma finiteModuleClosedSupport_coe (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (finiteModuleClosedSupport R M : Set (PrimeSpectrum R)) = Module.support R M :=
  Module.support_eq_zeroLocus.symm

lemma support_subset_finiteModuleClosedSupport
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.support R M ⊆ finiteModuleClosedSupport R M := by
  rw [finiteModuleClosedSupport_coe]

/-- Finite length of the tensor product places the intersection of supports at the closed point. -/
lemma finiteModuleClosedSupport_inf_le_maximal [IsLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤) :
    finiteModuleClosedSupport R M ⊓ finiteModuleClosedSupport R N ≤
      supportZeroLocus (maximalIdeal R) := by
  intro p hp
  have hM : p ∈ Module.support R M := by
    simpa only [← finiteModuleClosedSupport_coe R M] using hp.1
  have hN : p ∈ Module.support R N := by
    simpa only [← finiteModuleClosedSupport_coe R N] using hp.2
  have ht : p ∈ Module.support R (M ⊗[R] N) := by
    rw [support_tensorProduct]
    exact ⟨hM, hN⟩
  have he := eq_maximalIdeal
    (isMaximal_of_mem_support_of_isFiniteLength (M ⊗[R] N) (Module.length_ne_top_iff.mp hfin) p ht)
  change maximalIdeal R ≤ p.asIdeal
  exact le_of_eq he.symm
end SerrePositivity

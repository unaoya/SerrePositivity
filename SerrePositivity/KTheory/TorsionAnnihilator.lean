module
public import SerrePositivity.KTheory.G0Torsion

/-! # A single annihilator for a finite localization-torsion module -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R] {P : Submonoid R}
  {M : Type u} [AddCommGroup M] [Module R M]

namespace IsModuleSTorsion
/-- A finite set of torsion elements admits a common annihilator in the multiplicative set. -/
lemma exists_annihilator_finset (h : IsModuleSTorsion P M) (t : Finset M) :
    ∃ r ∈ P, ∀ m ∈ t, r • m = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, P.one_mem, by simp⟩
  | @insert m t hm ih =>
    obtain ⟨r, hr, er⟩ := h m
    obtain ⟨s, hs, es⟩ := ih
    refine ⟨s * r, P.mul_mem hs hr, ?_⟩
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · simp [mul_smul, er]
    · rw [mul_comm, mul_smul, es n hn, smul_zero]

/-- Finite generation turns elementwise torsion into a uniform annihilator. -/
lemma exists_annihilating_mem [Module.Finite R M] (h : IsModuleSTorsion P M) :
    ∃ r ∈ P, ∀ m : M, r • m = 0 := by
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R) (M := M)
  obtain ⟨r, hr, er⟩ := h.exists_annihilator_finset t
  refine ⟨r, hr, fun m => ?_⟩
  have hm : m ∈ Submodule.span R (t : Set M) := by rw [ht]; trivial
  induction hm using Submodule.span_induction with
  | mem m hm => exact er m hm
  | zero => exact smul_zero r
  | add m n hm hn em en => simp [smul_add, em, en]
  | smul a m hm em => rw [smul_comm, em, smul_zero]

lemma iff_exists_annihilating_mem [Module.Finite R M] :
    IsModuleSTorsion P M ↔ ∃ r ∈ P, ∀ m : M, r • m = 0 :=
  ⟨exists_annihilating_mem, fun ⟨r, hr, er⟩ m => ⟨r, hr, er m⟩⟩
end IsModuleSTorsion

/-- A zero localization of a finite module admits a single annihilator. -/
lemma exists_annihilating_mem_of_localized_zero [Module.Finite R M]
    (h : Subsingleton (LocalizedModule P M)) : ∃ r ∈ P, ∀ m : M, r • m = 0 :=
  (IsModuleSTorsion.iff_localized_zero.mpr h).exists_annihilating_mem

/-- An annihilator puts the support in its principal vanishing locus. -/
lemma module_support_subset_zeroLocus_of_annihilator (r : R) (h : ∀ m : M, r • m = 0) :
    Module.support R M ⊆ supportZeroLocus (Ideal.span ({r} : Set R)) := by
  intro p hp
  change Ideal.span ({r} : Set R) ≤ p.asIdeal
  apply Ideal.span_le.mpr
  intro a ha
  have har : a = r := Set.mem_singleton_iff.mp ha
  subst a
  by_contra hr
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hp
  exact hm r hr (h m)

/-- A supported torsion module has a uniformly smaller closed support. -/
lemma exists_annihilator_supportedOn
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (M : SupportedFGModuleOn Z)
    (h : IsModuleSTorsion P M.obj) :
    ∃ r ∈ P, finiteModuleSupportedOn
      (Z ⊓ supportZeroLocus (Ideal.span ({r} : Set R))) M.obj := by
  obtain ⟨r, hr, er⟩ := h.exists_annihilating_mem
  exact ⟨r, hr, M.property.1, fun p hp =>
    ⟨M.property.2 hp, module_support_subset_zeroLocus_of_annihilator r er hp⟩⟩
end SerrePositivity

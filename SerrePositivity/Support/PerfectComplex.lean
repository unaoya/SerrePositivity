module

public import SerrePositivity.PerfectComplex.OrdinaryEuler
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Homological support of bounded finite complexes

This file is independent of Lemma 3.5 and normalized Euler evaluation.
It connects support of homology to a common power annihilator. The further
step from homological support to null homotopies will be developed here.
It is essential to allow a larger exponent at that further step: a map
vanishing on homology need not itself be null-homotopic.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T]

/-- Every homology module is supported on the closed set defined by `I`. -/
def HasHomologySupport (I : Ideal T) (P : CochainComplex (ModuleCat.{u} T) ℤ) : Prop :=
  ∀ i, Module.support T (P.homology i) ⊆ PrimeSpectrum.zeroLocus I

variable [IsNoetherianRing T]

/-- For complexes of finite modules, support is equivalent to containment in
the radical of the homology annihilator. -/
lemma homologySupport_iff_le_radical_annihilator (I : Ideal T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (hfinite : ∀ i, Module.Finite T (P.X i)) :
    HasHomologySupport I P ↔ ∀ i, I ≤ (Module.annihilator T (P.homology i)).radical := by
  unfold HasHomologySupport
  apply forall_congr'
  intro i
  have := hfinite i
  have := homology_moduleFinite P i
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]

/-- Homological support gives a power annihilator at each degree. -/
lemma homology_pow_torsion_of_support (I : Ideal T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (hfinite : ∀ i, Module.Finite T (P.X i))
    (hP : HasHomologySupport I P) (i : ℤ) :
    ∃ n : ℕ, Module.IsTorsionBySet T (P.homology i) (I ^ n : Ideal T) := by
  have h := (homologySupport_iff_le_radical_annihilator I P hfinite).mp hP i
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h I.fg_of_isNoetherianRing
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  exact hn

/-- Boundedness permits one exponent for all homology modules. -/
theorem exists_common_pow_annihilator_of_homologySupport (I : Ideal T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (hfinite : ∀ i, Module.Finite T (P.X i))
    (hbounded : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : HasHomologySupport I P) :
    ∃ n : ℕ, ∀ i, Module.IsTorsionBySet T (P.homology i) (I ^ n : Ideal T) := by
  classical
  obtain ⟨a, b, hab⟩ := hbounded
  choose n hn using homology_pow_torsion_of_support I P hfinite hP
  refine ⟨(Finset.Icc a b).sup n, fun i ↦ ?_⟩
  by_cases hi : i ∈ Finset.Icc a b
  · have hpow : I ^ (Finset.Icc a b).sup n ≤ I ^ n i :=
      Ideal.pow_le_pow_right (Finset.le_sup hi)
    intro x r
    exact @hn i x ⟨r, hpow r.property⟩
  · have hz : IsZero (P.homology i) :=
      (P.sc i).isZero_homology_of_isZero_X₂ (hab i (by simp only [Finset.mem_Icc] at hi; omega))
    have := ModuleCat.subsingleton_of_isZero hz
    intro x r
    exact Subsingleton.elim _ _

end SerrePositivity

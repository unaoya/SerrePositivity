module
public import SerrePositivity.CommutativeAlgebra.PrimeDimensionBounds
public import SerrePositivity.CommutativeAlgebra.RegularSequenceUnmixedness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.RingTheory.Flat.Localization

/-! # Maximal regular sequences inside a prime ideal -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open RingTheory.Sequence IsLocalRing
open scoped Pointwise
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The length of a regular sequence is bounded by the finite dimension of the ring. -/
lemma regularSequence_length_le_dimToNat (rs : List R) (h : IsRegular R rs) :
    rs.length ≤ dimToNat (ringKrullDim R) := by
  have hn : Ideal.ofList rs ≠ ⊤ := by
    simpa using h.top_ne_smul.symm
  have : Nontrivial (R ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.mpr hn
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs h
  have hb : (rs.length : WithBot ℕ∞) ≤ ringKrullDim R := by
    rw [← hdim]
    exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial
  rw [← natCast_dimToNat_ringKrullDim R] at hb
  exact_mod_cast hb

/-- There is a longest regular sequence among those lying in a given prime. -/
lemma exists_maximal_regularSequence_in_prime (p : PrimeSpectrum R) :
    ∃ rs : List R, IsRegular R rs ∧ (∀ x ∈ rs, x ∈ p.asIdeal) ∧
      ∀ s : List R, IsRegular R s → (∀ x ∈ s, x ∈ p.asIdeal) → s.length ≤ rs.length := by
  let T : Set ℕ := {n | ∃ rs : List R, IsRegular R rs ∧
    (∀ x ∈ rs, x ∈ p.asIdeal) ∧ rs.length = n}
  have hne : T.Nonempty := ⟨0, [], .nil R R, by simp, rfl⟩
  have hb : BddAbove T := ⟨dimToNat (ringKrullDim R), by
    rintro n ⟨rs, hrs, _, rfl⟩
    exact regularSequence_length_le_dimToNat rs hrs⟩
  obtain ⟨n, hn, hmax⟩ := hb.exists_isGreatest_of_nonempty hne
  obtain ⟨rs, hrs, hp, hlen⟩ := hn
  refine ⟨rs, hrs, hp, fun s hs hsp => ?_⟩
  rw [hlen]
  exact hmax ⟨s, hs, hsp, rfl⟩

/-- No element of the prime can be regular on the quotient by a longest sequence. -/
lemma maximal_regularSequence_no_regular_extension (p : PrimeSpectrum R) (rs : List R)
    (hrs : IsRegular R rs) (hp : ∀ x ∈ rs, x ∈ p.asIdeal)
    (hmax : ∀ s : List R, IsRegular R s → (∀ x ∈ s, x ∈ p.asIdeal) → s.length ≤ rs.length)
    (x : R) (hx : x ∈ p.asIdeal) : ¬ IsSMulRegular (R ⧸ Ideal.ofList rs) x := by
  intro hreg
  have hweak : IsWeaklyRegular R (rs ++ [x]) := by
    apply (isWeaklyRegular_append_iff R rs [x]).mpr
    refine ⟨hrs.toIsWeaklyRegular, ?_⟩
    rw [show (Ideal.ofList rs • ⊤ : Submodule R R) = Ideal.ofList rs by simp]
    exact (isWeaklyRegular_singleton_iff _ x).mpr hreg
  have hmem : ∀ y ∈ rs ++ [x], y ∈ p.asIdeal := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hp y hy
    · obtain rfl := List.mem_singleton.mp hy
      exact hx
  have hregular : IsRegular R (rs ++ [x]) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      (fun y hy => (le_maximalIdeal p.isPrime.ne_top) (hmem y hy))).mpr hweak
  have hlen := hmax (rs ++ [x]) hregular hmem
  simp only [List.length_append, List.length_singleton] at hlen
  omega

/-- A longest regular sequence detects an associated prime containing the original prime. -/
lemma exists_associatedPrime_above_maximal_regularSequence (p : PrimeSpectrum R) (rs : List R)
    (hrs : IsRegular R rs) (hp : ∀ x ∈ rs, x ∈ p.asIdeal)
    (hmax : ∀ s : List R, IsRegular R s → (∀ x ∈ s, x ∈ p.asIdeal) → s.length ≤ rs.length) :
    ∃ q : Ideal R, q ∈ associatedPrimes R (R ⧸ Ideal.ofList rs) ∧ p.asIdeal ≤ q := by
  let Q := R ⧸ Ideal.ofList rs
  have hsub : (p.asIdeal : Set R) ⊆ ⋃ q ∈ associatedPrimes R Q, (q : Set R) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    intro x hx
    have hn := maximal_regularSequence_no_regular_extension p rs hrs hp hmax x hx
    rw [isSMulRegular_iff_right_eq_zero_of_smul] at hn
    push Not at hn
    obtain ⟨m, hm, hne⟩ := hn
    exact ⟨m, hne, hm⟩
  exact (Ideal.subset_union_prime_finite (associatedPrimes.finite R Q)
    (f := id) 0 0 (fun q hq _ _ => hq.isPrime)).mp hsub

/-- A regular sequence lying in a prime has length bounded by that prime's height.
Only flat localization and the dimension bound for regular sequences are used. -/
lemma regularSequence_length_le_primeHeight (p : PrimeSpectrum R) (rs : List R)
    (hrs : IsRegular R rs) (hp : ∀ x ∈ rs, x ∈ p.asIdeal) :
    (rs.length : ℕ∞) ≤ p.asIdeal.height := by
  let B := Localization.AtPrime p.asIdeal
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing p.asIdeal.primeCompl B inferInstance
  have : Module.Flat R B := IsLocalization.flat B p.asIdeal.primeCompl
  have hR : IsWeaklyRegular B rs :=
    ((TensorProduct.rid R B).isWeaklyRegular_congr rs).mp
      (hrs.toIsWeaklyRegular.isWeaklyRegular_lTensor (M₂ := B))
  have hB : IsWeaklyRegular B (rs.map (algebraMap R B)) :=
    (isWeaklyRegular_map_algebraMap_iff B B rs).mpr hR
  have hm : ∀ x ∈ rs.map (algebraMap R B), x ∈ maximalIdeal B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal B]
    exact Ideal.mem_map_of_mem _ (hp y hy)
  have hreg : IsRegular B (rs.map (algebraMap R B)) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hB
  have hn : Ideal.ofList (rs.map (algebraMap R B)) ≠ ⊤ := by
    simpa using hreg.top_ne_smul.symm
  have : Nontrivial (B ⧸ Ideal.ofList (rs.map (algebraMap R B))) :=
    Ideal.Quotient.nontrivial_iff.mpr hn
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hreg
  have hlen : ((rs.map (algebraMap R B)).length : WithBot ℕ∞) ≤ ringKrullDim B := by
    rw [← hdim]
    exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial
  rw [List.length_map, IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal B] at hlen
  exact WithBot.coe_le_coe.mp hlen

/-- The complete maximal-sequence witness needed for the prime dimension formula. -/
lemma exists_regularSequence_associatedPrime_above (p : PrimeSpectrum R) :
    ∃ (rs : List R) (q : Ideal R), IsRegular R rs ∧ (∀ x ∈ rs, x ∈ p.asIdeal) ∧
      q ∈ associatedPrimes R (R ⧸ Ideal.ofList rs) ∧ p.asIdeal ≤ q ∧
      (rs.length : ℕ∞) ≤ p.asIdeal.height := by
  obtain ⟨rs, hrs, hp, hmax⟩ := exists_maximal_regularSequence_in_prime p
  obtain ⟨q, hq, hpq⟩ := exists_associatedPrime_above_maximal_regularSequence p rs hrs hp hmax
  exact ⟨rs, q, hrs, hp, hq, hpq, regularSequence_length_le_primeHeight p rs hrs hp⟩
end SerrePositivity

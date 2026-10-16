module
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Ideal.Maps

/-! # Clearing a finite principal cover of R[1/g] back to the original ring -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity

/-- The original g times the chosen numerators of a cover of R[1/g] generate an
ideal containing a power of g. No regularity or nonzero condition on g is required. -/
theorem exists_pow_mem_span_scaled_cover_numerators
    {R : Type u} [CommRing R] (g : R) (t : Finset (Localization.Away g))
    (ht : Ideal.span (t : Set (Localization.Away g)) = ⊤) :
    ∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun x : t =>
      g * (IsLocalization.Away.sec g x.1).1)) := by
  let L := Localization.Away g
  let J : Ideal R := Ideal.span (Set.range (fun x : t =>
    g * (IsLocalization.Away.sec g x.1).1))
  have hmap : J.map (algebraMap R L) = ⊤ := by
    apply top_unique
    rw [← ht]
    apply Ideal.span_le.mpr
    intro x hx
    let u := IsLocalization.Away.sec g x
    have heq : algebraMap R L (g * u.1) = (algebraMap R L g) ^ (u.2 + 1) * x := by
      dsimp only [u]
      rw [map_mul, ← IsLocalization.Away.sec_spec g x, map_pow, pow_succ]
      ac_rfl
    apply ((J.map (algebraMap R L)).unit_mul_mem_iff_mem
      ((IsLocalization.Away.algebraMap_isUnit (S := L) g).pow (u.2 + 1))).mp
    rw [← heq]
    exact Ideal.mem_map_of_mem (algebraMap R L) (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩)
  have hone : algebraMap R L (1 : R) ∈ J.map (algebraMap R L) := by
    rw [hmap]
    trivial
  obtain ⟨m, hm, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers g) L J 1).mp hone
  obtain ⟨N, rfl⟩ := hm
  exact ⟨N, by simpa only [mul_one] using hmem⟩

/-- Local uniform annihilators on a finite cover give one exponent for the entire
module family. The family and its modules need not be finite or finitely generated. -/
theorem exists_uniform_family_pow_smul_zero_of_cover
    {R : Type u} [CommRing R] {ι : Type*} (X : ι → Type u)
    [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] (g : R) (t : Finset R)
    (hcover : ∃ k : ℕ, g ^ k ∈ Ideal.span (t : Set R))
    (hzero : ∀ a ∈ t, ∃ N : ℕ, ∀ i, ∀ x : X i, a ^ N • x = 0) :
    ∃ N : ℕ, ∀ i, ∀ x : X i, g ^ N • x = 0 := by
  let J : Ideal R := ⨅ i, Module.annihilator R (X i)
  have hspan : Ideal.span (t : Set R) ≤ J.radical := by
    apply Ideal.span_le.mpr
    intro a ha
    obtain ⟨N, hN⟩ := hzero a ha
    apply Ideal.mem_radical_iff.mpr
    refine ⟨N, ?_⟩
    change a ^ N ∈ ⨅ i, Module.annihilator R (X i)
    simp only [Submodule.mem_iInf]
    intro i
    exact Module.mem_annihilator.mpr (hN i)
  obtain ⟨k, hk⟩ := hcover
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp (Ideal.mem_radical_of_pow_mem (hspan hk))
  refine ⟨N, ?_⟩
  change g ^ N ∈ ⨅ i, Module.annihilator R (X i) at hN
  simp only [Submodule.mem_iInf] at hN
  intro i
  exact Module.mem_annihilator.mp (hN i)

end SerrePositivity

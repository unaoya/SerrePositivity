module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Scalar-divisible conormal modules give idempotent images in all power quotients -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Divisibility on I/I² supplies idempotence of the actual image of I modulo aⁿ,
including n=0. No completeness, regularity, or Noetherian hypotheses are needed. -/
lemma ideal_mod_power_idempotent_of_conormal_surjective {R : Type u} [CommRing R] (a : R) (I : Ideal R)
    (h : Function.Surjective (fun x : I.Cotangent => a • x)) (n : ℕ) :
    IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))) := by
  have hn : Function.Surjective (fun x : I.Cotangent => a ^ n • x) := by
    induction n with
    | zero =>
      intro x
      exact ⟨x, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨z, hz⟩ := h y
      refine ⟨z, ?_⟩
      change a ^ (n + 1) • z = x
      change a ^ n • y = x at hy
      change a • z = y at hz
      rw [pow_succ, mul_smul, hz, hy]
  let φ := Ideal.Quotient.mk (Ideal.span {a ^ n})
  apply le_antisymm Ideal.mul_le_left
  rw [← Ideal.map_mul, Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨y, hy⟩ := hn (I.toCotangent ⟨x, hx⟩)
  obtain ⟨z, rfl⟩ := I.toCotangent_surjective y
  change a ^ n • I.toCotangent z = I.toCotangent ⟨x, hx⟩ at hy
  have hz : I.toCotangent (⟨x, hx⟩ - a ^ n • z) = 0 := by
    rw [map_sub, map_smul, hy, sub_self]
  have hmem : x - a ^ n * (z : R) ∈ I * I := by
    have hz₂ := (I.toCotangent_eq_zero _).mp hz
    change x - a ^ n * (z : R) ∈ I ^ 2 at hz₂
    simpa only [pow_two] using hz₂
  have hφ : φ (a ^ n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hm := Ideal.mem_map_of_mem φ hmem
  change φ x ∈ (I * I).map φ
  simpa only [map_sub, map_mul, hφ, zero_mul, sub_zero] using hm

end SerrePositivity

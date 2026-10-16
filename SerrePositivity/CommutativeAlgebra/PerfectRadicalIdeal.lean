module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Ideal.Cotangent

/-! # Radical ideals in rings with surjective power maps are idempotent -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable (R : Type u) [CommRing R] (I : Ideal R)

/-- A radical ideal is idempotent when every element admits an n-th root, n≥2. -/
lemma radicalIdeal_idempotent_of_power_surjective (n : ℕ) (hn : 2 ≤ n)
    (hroot : ∀ x : R, ∃ y : R, y ^ n = x) (hI : I.IsRadical) : IsIdempotentElem I := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  obtain ⟨y, hy⟩ := hroot x
  have hyI : y ∈ I := hI ⟨n, by simpa only [hy] using hx⟩
  have hyN : y ^ (n - 1) ∈ I := I.pow_mem_of_mem hyI _ (by omega)
  have he : y * y ^ (n - 1) = x := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega), hy]
  rw [← he]
  exact Ideal.mul_mem_mul hyI hyN

/-- In a perfect characteristic-p ring, every radical ideal is idempotent. -/
lemma radicalIdeal_idempotent_of_perfectRing (p : ℕ) [Fact p.Prime]
    [CharP R p] [PerfectRing R p] (hI : I.IsRadical) : IsIdempotentElem I :=
  radicalIdeal_idempotent_of_power_surjective R I p (Fact.out : p.Prime).two_le
    (fun x => ⟨(frobeniusEquiv R p).symm x, frobeniusEquiv_symm_pow_p R p x⟩) hI

/-- In particular the existing conormal module of a radical ideal is zero. -/
lemma radicalIdeal_cotangent_subsingleton_of_perfectRing (p : ℕ) [Fact p.Prime]
    [CharP R p] [PerfectRing R p] (hI : I.IsRadical) : Subsingleton I.Cotangent :=
  (I.cotangent_subsingleton_iff).mpr (radicalIdeal_idempotent_of_perfectRing R I p hI)

end SerrePositivity

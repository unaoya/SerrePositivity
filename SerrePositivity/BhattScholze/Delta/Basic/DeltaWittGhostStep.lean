module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.NumberTheory.Basic
public import Mathlib.Logic.Function.Iterate

/-! # δFrobeniusのghost係数を一段延長する可除性

既存のp乗合同の可除性から、次のWitt ghost係数の存在を示す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δFrobeniusとp乗の合同は、p^k乗後にはp^(k+1)まで強まる。 -/
theorem frobeniusLift_pow_congruence (D : DeltaStructure p A) (a : A) (k : ℕ) :
    (p : A) ^ (k + 1) ∣ (D.frobeniusLift a) ^ (p ^ k) - (a ^ p) ^ (p ^ k) := by
  apply dvd_sub_pow_of_dvd_sub
  exact ⟨D.delta a, by rw [D.frobeniusLift_apply]; ring⟩

/-- 前段のghost等式から、次の係数を作る差はp^(n+1)で割り切れる。 -/
theorem ghost_next_dvd (D : DeltaStructure p A) (a : A) (b : ℕ → A) (n : ℕ)
    (hb : D.frobeniusLift^[n] a =
      ∑ i ∈ Finset.range (n + 1), (p : A) ^ i * b i ^ (p ^ (n - i))) :
    (p : A) ^ (n + 1) ∣ D.frobeniusLift^[n + 1] a -
      ∑ i ∈ Finset.range (n + 1), (p : A) ^ i * b i ^ (p ^ (n + 1 - i)) := by
  rw [Function.iterate_succ_apply', hb, map_sum]
  simp only [map_mul, map_pow, map_natCast]
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hexp : n + 1 - i = n - i + 1 := by omega
  rw [← mul_sub, hexp, pow_succ' p (n - i), pow_mul]
  have he : n + 1 = i + (n - i + 1) := by omega
  rw [he, pow_add]
  exact mul_dvd_mul_left _ (D.frobeniusLift_pow_congruence (b i) (n - i))

/-- 前段までの係数に、次のghost等式を満たす係数を追加できる。 -/
theorem exists_next_ghost_coefficient (D : DeltaStructure p A) (a : A) (b : ℕ → A) (n : ℕ)
    (hb : D.frobeniusLift^[n] a =
      ∑ i ∈ Finset.range (n + 1), (p : A) ^ i * b i ^ (p ^ (n - i))) :
    ∃ c : A, D.frobeniusLift^[n + 1] a =
      (∑ i ∈ Finset.range (n + 1), (p : A) ^ i * b i ^ (p ^ (n + 1 - i))) +
        (p : A) ^ (n + 1) * c := by
  obtain ⟨c, hc⟩ := D.ghost_next_dvd a b n hb
  refine ⟨c, ?_⟩
  rw [← hc]
  ring

end SerrePositivity.BhattScholze.DeltaStructure

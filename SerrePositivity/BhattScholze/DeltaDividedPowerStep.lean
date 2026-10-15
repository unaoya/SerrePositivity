module

public import SerrePositivity.BhattScholze.DeltaResidueArithmetic

/-! # δ環の反復p除算とp典型分母

著者公開版Lemma 2.35の代数的入力。一般のpねじれを許す。
階乗分母全体・分冪構造・分冪包との同定は別工程。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ環でx^p=pzならz^pもpで割り切れる。p正則性は不要。 -/
theorem prime_dvd_divided_pow (D : DeltaStructure p A) {x z : A}
    (hx : x ^ p = (p : A) * z) : (p : A) ∣ z ^ p := by
  let I := Ideal.span {(p : A)}
  let q := Ideal.Quotient.mk I
  have hp : q (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have h := D.map_delta_pow_prime_of_zero q hp x
  rw [hx, D.map_delta_mul_of_prime_zero q hp,
    D.map_delta_prime_of_zero q hp, hp, zero_pow (Fact.out : p.Prime).ne_zero,
    zero_mul, one_mul, zero_add] at h
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_pow] using h))

/-- 一度x^p/pが存在すれば、c_(n+1)=c_n^p/pを全段で選べる。 -/
theorem exists_iterated_prime_division (D : DeltaStructure p A) {x z : A}
    (hx : x ^ p = (p : A) * z) :
    ∃ c : ℕ → A, c 0 = x ∧ c 1 = z ∧ ∀ n, (p : A) * c (n + 1) = c n ^ p := by
  let T := {t : A // (p : A) ∣ t ^ p}
  let next : T → T := fun t =>
    ⟨t.property.choose, D.prime_dvd_divided_pow t.property.choose_spec⟩
  let c : ℕ → A := fun n => if n = 0 then x else
    ((next^[n - 1]) ⟨z, D.prime_dvd_divided_pow hx⟩).val
  refine ⟨c, by simp [c], by simp [c], ?_⟩
  intro n
  cases n with
  | zero => simpa [c] using hx.symm
  | succ n =>
      simp only [c, Nat.succ_ne_zero, ↓reduceIte,
        Nat.succ_sub_one, Function.iterate_succ_apply']
      exact ((next^[n]) ⟨z, D.prime_dvd_divided_pow hx⟩).property.choose_spec.symm

/-- p典型反復除算に現れるpの指数。 -/
def primeDivisionExponent (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => p * primeDivisionExponent p n + 1

omit [Fact p.Prime] in
/-- 反復除算列の各項は、p冪分母を払うとx^(p^n)となる。 -/
theorem iterated_prime_division_denominator {x : A} {c : ℕ → A}
    (h₀ : c 0 = x) (hc : ∀ n, (p : A) * c (n + 1) = c n ^ p) (n : ℕ) :
    (p : A) ^ primeDivisionExponent p n * c n = x ^ p ^ n := by
  induction n with
  | zero => simp [primeDivisionExponent, h₀]
  | succ n ih =>
      calc
        (p : A) ^ primeDivisionExponent p (n + 1) * c (n + 1) =
            (p : A) ^ (p * primeDivisionExponent p n) * ((p : A) * c (n + 1)) := by
          rw [primeDivisionExponent, pow_succ, mul_assoc]
        _ = ((p : A) ^ primeDivisionExponent p n * c n) ^ p := by
          rw [hc, mul_pow, ← pow_mul, Nat.mul_comm p]
        _ = x ^ p ^ (n + 1) := by rw [ih, ← pow_mul, Nat.pow_succ]

omit [Fact p.Prime] in
/-- p正則環では、同じ初項を持つ反復p除算列は一意。 -/
theorem iterated_prime_division_unique
    (hpA : Function.Injective (fun t : A => (p : A) * t)) {c d : ℕ → A}
    (h₀ : c 0 = d 0) (hc : ∀ n, (p : A) * c (n + 1) = c n ^ p)
    (hd : ∀ n, (p : A) * d (n + 1) = d n ^ p) : c = d := by
  funext n
  induction n with
  | zero => exact h₀
  | succ n ih =>
      apply hpA
      change (p : A) * c (n + 1) = (p : A) * d (n + 1)
      rw [hc, hd, ih]

end SerrePositivity.BhattScholze.DeltaStructure

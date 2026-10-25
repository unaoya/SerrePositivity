module

public import SerrePositivity.BhattScholze.Delta.DeltaRing
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # p冪根を持つ元のrank 1性

BS著者公開版Lemma 2.32。δの積公式を(pδ(x))で割った商で反復し、
δ(x^p)がpδ(x)で割り切れることから一般δ環での可除性を証明する。
p正則性・自由δ環への帰着を使わない代数的な証明。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ(x^p)はpδ(x)で割り切れる。
(pδ(x))による商ではδ積公式の第三項が消え、通常の冪の微分と同じ帰納式になる。 -/
theorem p_mul_delta_dvd_delta_pow (D : DeltaStructure p A) (x : A) :
    (p : A) * D.delta x ∣ D.delta (x ^ p) := by
  let I := Ideal.span {(p : A) * D.delta x}
  let q := Ideal.Quotient.mk I
  have hz : q (p : A) * q (D.delta x) = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hpow (m : ℕ) : q (D.delta (x ^ (m + 1))) =
      (m + 1 : ℕ) * q x ^ (p * m) * q (D.delta x) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, D.delta_mul, map_add, map_add, map_mul, map_mul, map_mul,
          map_mul, map_pow, map_pow, ih]
        have hpowers : (q x ^ (m + 1)) ^ p = q x ^ (p * m) * q x ^ p := by
          rw [← pow_mul, Nat.add_mul, Nat.one_mul, Nat.mul_comm m p, pow_add]
        rw [hpowers]
        have herr : q (p : A) * ((m + 1 : ℕ) * q x ^ (p * m) * q (D.delta x)) *
            q (D.delta x) = 0 := by
          calc
            _ = ((m + 1 : ℕ) * q x ^ (p * m) * q (D.delta x)) *
                (q (p : A) * q (D.delta x)) := by ring
            _ = 0 := by rw [hz, mul_zero]
        rw [herr, add_zero, Nat.mul_succ, pow_add]
        simp only [map_pow]
        push_cast
        ring
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := hpow (p - 1)
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).pos] at h
  rw [h]
  calc
    (p : A ⧸ I) * q x ^ (p * (p - 1)) * q (D.delta x) =
        q x ^ (p * (p - 1)) * (q (p : A) * q (D.delta x)) := by rw [map_natCast]; ring
    _ = 0 := by rw [hz, mul_zero]

/-- δ(x^(p^n))はp^nδ(x)で割り切れる。一般δ環で成立し、pねじれを許す。 -/
theorem pow_mul_delta_dvd_delta_pow (D : DeltaStructure p A) (x : A) (n : ℕ) :
    (p : A) ^ n * D.delta x ∣ D.delta (x ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := D.p_mul_delta_dvd_delta_pow (x ^ p ^ n)
      have hdiv := (mul_dvd_mul_left (p : A) ih).trans h
      simpa only [pow_succ, ← pow_mul, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- BS Lemma 2.32の可除性：δ(x^(p^n))∈(p^n)。p正則性は要求しない。 -/
theorem pow_p_dvd_delta_pow (D : DeltaStructure p A) (x : A) (n : ℕ) :
    (p : A) ^ n ∣ D.delta (x ^ p ^ n) :=
  (dvd_mul_right ((p : A) ^ n) (D.delta x)).trans (D.pow_mul_delta_dvd_delta_pow x n)

/-- p進分離なδ環で、すべてのp^n乗根を持つ元はrank 1、すなわちδ(y)=0。
根の両立性は要求しない（BS著者版Lemma 2.32の後半）。 -/
theorem delta_eq_zero_of_has_pow_roots (D : DeltaStructure p A)
    [IsHausdorff (Ideal.span {(p : A)}) A] (y : A)
    (hy : ∀ n : ℕ, ∃ x : A, x ^ p ^ n = y) : D.delta y = 0 := by
  apply IsHausdorff.haus' (I := Ideal.span {(p : A)})
  intro n
  obtain ⟨x, hx⟩ := hy n
  have h := D.pow_p_dvd_delta_pow x n
  rw [hx] at h
  simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] using
    (Ideal.mem_span_singleton.mpr h)

end SerrePositivity.BhattScholze.DeltaStructure

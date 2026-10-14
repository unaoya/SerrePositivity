module

public import Mathlib.RingTheory.WittVector.MulCoeff
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.Algebra.Polynomial.Monic

/-! # 零定数係数のWitt除数の全段三角形表示

Verschiebungで一段下げて既存のWitt積係数公式を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 零定数係数の除数の第n+2積係数は、次の変数のp乗と下位係数だけで表される。 -/
theorem wittDivision_exists_triangular_remainder
    (hp : (p : R) = 0) (x : WittVector p R) (hx : x.coeff 0 = 0) (n : ℕ) :
    ∃ r : (Fin (n + 1) → R) → R, ∀ y : WittVector p R,
      (x * y).coeff (n + 2) =
        x.coeff 1 ^ (p ^ (n + 1)) * y.coeff (n + 1) ^ p +
          r (WittVector.truncateFun (n + 1) y) := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl h =>
      let := h
      exact ⟨fun _ => 0, fun _ => Subsingleton.elim _ _⟩
  | inr h =>
      let := h
      let : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
      let z : WittVector p R := WittVector.mk p (fun i => x.coeff (i + 1))
      have hV : WittVector.verschiebung z = x := by
        ext i
        cases i with
        | zero => simpa only [WittVector.verschiebung_coeff_zero] using hx.symm
        | succ i => simp only [WittVector.verschiebung_coeff_succ, z, WittVector.coeff_mk]
      let r : (Fin (n + 1) → R) → R := fun v =>
        x.coeff (n + 2) * (v ⟨0, Nat.zero_lt_succ n⟩ ^ p) ^ (p ^ (n + 1)) +
          WittVector.nthRemainder p n (WittVector.truncateFun (n + 1) z) (fun i => v i ^ p)
      refine ⟨r, ?_⟩
      intro y
      have he : (x * y).coeff (n + 2) = (z * WittVector.frobenius y).coeff (n + 1) := by
        calc
          _ = (WittVector.verschiebung z * y).coeff (n + 2) := by rw [hV]
          _ = (WittVector.verschiebung (z * WittVector.frobenius y)).coeff (n + 2) := by
            rw [WittVector.verschiebung_mul_frobenius]
          _ = _ := WittVector.verschiebung_coeff_succ _ _
      rw [he, WittVector.nthRemainder_spec]
      simp only [z, WittVector.coeff_mk, WittVector.coeff_frobenius_charP]
      have ht : WittVector.truncateFun (n + 1) (WittVector.frobenius y) =
          fun i => (WittVector.truncateFun (n + 1) y i) ^ p := by
        funext i
        exact WittVector.coeff_frobenius_charP p y i.val
      rw [ht]
      simp only [r, z, WittVector.truncateFun, TruncatedWittVector.mk,
        WittVector.coeff_mk]
      ring

/-- 単元第1係数のWitt除数について、全段の積係数方程式はモニックp乗方程式。 -/
theorem wittDivision_exists_monic_equation
    (hp : (p : R) = 0) (x : WittVector p R) (hx : x.coeff 0 = 0)
    (u : Rˣ) (hu : (u : R) = x.coeff 1) (n : ℕ) :
    ∃ r : (Fin (n + 1) → R) → R, ∀ (y : WittVector p R) (c : R),
      (Polynomial.X ^ p - Polynomial.C
        (((u⁻¹ : Rˣ) : R) ^ (p ^ (n + 1)) *
          (c - r (WittVector.truncateFun (n + 1) y)))).Monic ∧
      ((x * y).coeff (n + 2) = c ↔
        Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.C
          (((u⁻¹ : Rˣ) : R) ^ (p ^ (n + 1)) *
            (c - r (WittVector.truncateFun (n + 1) y)))) (y.coeff (n + 1))) := by
  obtain ⟨r, hr⟩ := wittDivision_exists_triangular_remainder hp x hx n
  refine ⟨r, fun y c => ?_⟩
  constructor
  · exact Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero
  · rw [hr y, ← hu]
    change _ ↔ Polynomial.eval _ _ = 0
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero]
    constructor
    · intro h
      have he : (u : R) ^ (p ^ (n + 1)) * y.coeff (n + 1) ^ p =
          c - r (WittVector.truncateFun (n + 1) y) := by
        rw [← h]
        ring
      calc
        y.coeff (n + 1) ^ p =
            (((u⁻¹ : Rˣ) : R) ^ (p ^ (n + 1)) * (u : R) ^ (p ^ (n + 1))) *
              y.coeff (n + 1) ^ p := by rw [← mul_pow]; simp
        _ = _ := by rw [mul_assoc, he]
    · intro h
      rw [h, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
      ring

end SerrePositivity.BhattScholze

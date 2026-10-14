module

public import SerrePositivity.CommutativeAlgebra.WittCoefficientOne
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # distinguishedなWitt関係式によるp冪ねじれの降下

完全被約係数環のWitt環で、第1係数が単元の関係式による商のp冪ねじれはpで消える。
第0・第1係数の積の比較とWitt環でのpのキャンセルを使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    [PerfectRing R p] [IsReduced R]

omit [PerfectRing R p] in
/-- 第1係数が単元の関係式と、二つの零係数を持つ積から、因子の第0係数は零。 -/
theorem witt_factor_coeff_zero_of_distinguished (ξ a : WittVector p R)
    (hξ : IsUnit (ξ.coeff 1)) (h0 : (ξ * a).coeff 0 = 0) (h1 : (ξ * a).coeff 1 = 0) :
    a.coeff 0 = 0 := by
  have hz : ξ.coeff 0 * a.coeff 0 = 0 := by
    simpa only [WittVector.mul_coeff_zero] using h0
  have hf : ξ.coeff 0 ^ p * a.coeff 1 + ξ.coeff 1 * a.coeff 0 ^ p = 0 := by
    simpa only [witt_mul_coeff_one, CharP.cast_eq_zero, zero_mul, add_zero] using h1
  have hn : (a.coeff 0) ^ (p + p) = 0 := by
    apply hξ.mul_right_eq_zero.mp
    calc
      _ = (ξ.coeff 0 ^ p * a.coeff 1 + ξ.coeff 1 * a.coeff 0 ^ p) * a.coeff 0 ^ p -
          a.coeff 1 * (ξ.coeff 0 * a.coeff 0) ^ p := by
        rw [pow_add, mul_pow]
        ring
      _ = 0 := by rw [hf, hz, zero_pow (Fact.out : p.Prime).ne_zero]; simp
  exact IsReduced.eq_zero _ ⟨p + p, hn⟩

/-- distinguished関係式によるWitt商のp冪ねじれはpで消える。 -/
theorem witt_distinguished_dvd_p_mul_of_dvd_p_pow_mul (ξ b : WittVector p R)
    (hξ : IsUnit (ξ.coeff 1)) (n : ℕ) (hn : 0 < n)
    (hdiv : ξ ∣ (p : WittVector p R) ^ n * b) : ξ ∣ (p : WittVector p R) * b := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa only [zero_add, pow_one] using hdiv
    · obtain ⟨a, ha⟩ := hdiv
      have h0 : (ξ * a).coeff 0 = 0 := by
        rw [← ha, mul_comm]
        exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).mp
          (Ideal.mem_span_singleton.mpr ⟨b, mul_comm _ _⟩) 0 (by omega)
      have h1 : (ξ * a).coeff 1 = 0 := by
        rw [← ha, mul_comm]
        exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).mp
          (Ideal.mem_span_singleton.mpr ⟨b, mul_comm _ _⟩) 1 (by omega)
      have ha0 := witt_factor_coeff_zero_of_distinguished R p ξ a hξ h0 h1
      obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.mp
        ((WittVector.mem_span_p_iff_coeff_zero_eq_zero a).mpr ha0)
      have heq : (p : WittVector p R) * (ξ * a') =
          (p : WittVector p R) * ((p : WittVector p R) ^ n * b) := by
        calc
          _ = ξ * a := by rw [ha']; ac_rfl
          _ = _ := by rw [← ha, pow_succ]; ac_rfl
      have hcancel : ξ * a' = (p : WittVector p R) ^ n * b := by
        apply sub_eq_zero.mp
        apply WittVector.eq_zero_of_p_mul_eq_zero
        rw [mul_comm, mul_sub, heq, sub_self]
      exact ih (Nat.pos_of_ne_zero hn0) ⟨a', hcancel.symm⟩

/-- p+[q]^N aという関係式でaの第0係数が単元なら、pねじれは[q]で消える。 -/
theorem witt_teichmuller_mul_dvd_of_p_mul_dvd (q : R) (a b : WittVector p R)
    (N : ℕ) (hN : 0 < N) (ha : IsUnit (a.coeff 0))
    (hdiv : (p : WittVector p R) + WittVector.teichmuller p q ^ N * a ∣
      (p : WittVector p R) * b) :
    (p : WittVector p R) + WittVector.teichmuller p q ^ N * a ∣
      WittVector.teichmuller p q * b := by
  let ξ := (p : WittVector p R) + WittVector.teichmuller p q ^ N * a
  obtain ⟨d, hd⟩ := hdiv
  have hco : q ^ N * d.coeff 0 = 0 := by
    have hh := congrArg (WittVector.constantCoeff : WittVector p R →+* R) hd
    change _ = WittVector.constantCoeff (ξ * d) at hh
    simp only [ξ, map_mul, map_add, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul,
      zero_add, WittVector.constantCoeff, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, WittVector.teichmuller_coeff_zero] at hh
    apply ha.mul_right_eq_zero.mp
    calc
      _ = (q ^ N * a.coeff 0) * d.coeff 0 := by ac_rfl
      _ = 0 := hh.symm
  have hqd : q * d.coeff 0 = 0 := by
    apply IsReduced.eq_zero
    refine ⟨N, ?_⟩
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    rw [hn] at hco ⊢
    calc
      _ = (q ^ (n + 1) * d.coeff 0) * d.coeff 0 ^ n := by
        rw [mul_pow, pow_succ (d.coeff 0)]
        ac_rfl
      _ = 0 := by rw [hco, zero_mul]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero (WittVector.teichmuller p q * d)).mpr
      (by simpa only [WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] using hqd))
  have heq : (p : WittVector p R) * (WittVector.teichmuller p q * b) =
      (p : WittVector p R) * (ξ * v) := by
    calc
      _ = WittVector.teichmuller p q * ((p : WittVector p R) * b) := by ac_rfl
      _ = ξ * (WittVector.teichmuller p q * d) := by rw [hd]; dsimp only [ξ]; ac_rfl
      _ = _ := by rw [hv]; ac_rfl
  have hcancel : WittVector.teichmuller p q * b = ξ * v := by
    apply sub_eq_zero.mp
    apply WittVector.eq_zero_of_p_mul_eq_zero
    rw [mul_comm, mul_sub, heq, sub_self]
  exact ⟨v, hcancel⟩

end SerrePositivity

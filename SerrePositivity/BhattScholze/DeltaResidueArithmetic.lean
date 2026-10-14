module

public import SerrePositivity.BhattScholze.DeltaRankOne
public import SerrePositivity.BhattScholze.DeltaPrime

/-! # B4-6：通常剰余射の下でのδ反復計算

δは剰余環へ降りるとは仮定せず、源でδを計算してから環射で写す。
既存のWitt自然性・δ冪の可除性・δ(p)の合同式を再利用する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- pを消す任意の通常環射の下で、δ(p)は1となる。零終域も含む。 -/
theorem map_delta_prime_of_zero (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) : q (D.delta (p : A)) = 1 := by
  have hle : Ideal.span {(p : A)} ≤ RingHom.ker q :=
    (Ideal.span_singleton_le_iff_mem _).mpr hp
  have he := hle (D.delta_p_sub_one_mem)
  change q (D.delta (p : A) - 1) = 0 at he
  rw [map_sub, map_one, sub_eq_zero] at he
  exact he

/-- pを消す射の下でδ(x^p)は零。源のp正則性は不要。 -/
theorem map_delta_pow_prime_of_zero (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x : A) : q (D.delta (x ^ p)) = 0 := by
  obtain ⟨b, hb⟩ := D.p_mul_delta_dvd_delta_pow x
  rw [hb, map_mul, map_mul, hp, zero_mul, zero_mul]

/-- 左項が消える通常環射の下では、δの加法補正項も消える。 -/
theorem map_delta_add_of_left_zero (D : DeltaStructure p A) (q : A →+* B)
    (x y : A) (hx : q x = 0) : q (D.delta (x + y)) = q (D.delta x) + q (D.delta y) := by
  rw [D.delta_add, map_add, map_add]
  have hc : q ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1) = 0 := by
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
      WittVector.map_teichmuller, hx, WittVector.teichmuller_zero, zero_add]
    exact WittVector.teichmuller_coeff_pos p (q y) 1 (by decide)
  rw [hc, add_zero]

/-- 右項が消える場合のδ加法公式。 -/
theorem map_delta_add_of_right_zero (D : DeltaStructure p A) (q : A →+* B)
    (x y : A) (hy : q y = 0) : q (D.delta (x + y)) = q (D.delta x) + q (D.delta y) := by
  rw [add_comm x y, D.map_delta_add_of_left_zero q y x hy, add_comm]

/-- pを消す通常環射の下でのδ積公式。 -/
theorem map_delta_mul_of_prime_zero (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x y : A) :
    q (D.delta (x * y)) = (q x) ^ p * q (D.delta y) + q (D.delta x) * (q y) ^ p := by
  rw [D.delta_mul, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_pow,
    map_pow, hp, zero_mul, zero_mul, add_zero]

end SerrePositivity.BhattScholze.DeltaStructure

module

public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.Ideal.Maps

/-! # 完全標数p環の零化イデアルと主イデアル商 -/

@[expose] public noncomputable section
namespace SerrePositivity
variable (k : Type*) [CommRing k]

/-- 一元の零化イデアル。 -/
def principalAnnihilator (a : k) : Ideal k := (Submodule.span k {a}).annihilator

/-- 零化イデアルの所属条件。 -/
theorem mem_principalAnnihilator (a z : k) : z ∈ principalAnnihilator k a ↔ a * z = 0 := by
  rw [principalAnnihilator, Submodule.mem_annihilator_span_singleton]
  change z * a = 0 ↔ a * z = 0
  rw [mul_comm]

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- 完全環のp冪乗は全単射。 -/
theorem perfect_pow_pow_bijective (n : ℕ) : Function.Bijective (fun x : k ↦ x ^ p ^ n) := by
  have h := (PerfectRing.bijective_frobenius (R := k) (p := p)).iterate n
  change Function.Bijective (frobenius k p)^[n] at h
  constructor
  · intro x y he
    apply h.1
    simpa only [iterate_frobenius] using he
  · intro x
    obtain ⟨y, hy⟩ := h.2 x
    exact ⟨y, by simpa only [iterate_frobenius] using hy⟩

omit [CharP k p] in
/-- 完全環の零化イデアル内でp乗根を選べる。 -/
theorem principalAnnihilator_has_p_roots (a : k) (u : principalAnnihilator k a) :
    ∃ v : principalAnnihilator k a, (v : k) ^ p = u := by
  obtain ⟨v, hv⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 (u : k)
  have hu := (mem_principalAnnihilator k a u).mp u.property
  have hvann : a * v = 0 := by
    apply (PerfectRing.bijective_frobenius (R := k) (p := p)).1
    change (a * v) ^ p = (0 : k) ^ p
    change v ^ p = (u : k) at hv
    rw [mul_pow, hv]
    have h := pow_mul_eq_zero_of_le (a := a) (b := (u : k))
      (m := 1) (n := p) (Fact.out : p.Prime).one_lt.le (by simpa using hu)
    simpa only [zero_pow (Fact.out : p.Prime).ne_zero] using h
  exact ⟨⟨v, (mem_principalAnnihilator k a v).mpr hvann⟩, hv⟩

/-- aのp冪根もann(a)を零化する。 -/
theorem principalAnnihilator_killed_by_p_root (a r : k) (n : ℕ) (hr : r ^ p ^ n = a)
    (z : k) (hz : z ∈ principalAnnihilator k a) : r * z = 0 := by
  have ha := (mem_principalAnnihilator k a z).mp hz
  apply (perfect_pow_pow_bijective k p n).1
  change (r * z) ^ p ^ n = (0 : k) ^ p ^ n
  rw [mul_pow, hr]
  have h := pow_mul_eq_zero_of_le (a := z) (b := a) (m := 1) (n := p ^ n)
    (Nat.one_le_pow n p (Fact.out : p.Prime).pos)
    (by simpa only [pow_one, mul_comm] using ha)
  simpa only [mul_comm, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] using h

/-- 主イデアル商への零化イデアルの像。 -/
def quotientAnnihilatorImage (a : k) : Ideal (k ⧸ Ideal.span {a}) :=
  (principalAnnihilator k a).map (Ideal.Quotient.mk (Ideal.span {a}))

omit [CharP k p] in
/-- 商への像もイデアル内でp乗根を持つ。 -/
theorem quotientAnnihilatorImage_has_p_roots (a : k) (u : quotientAnnihilatorImage k a) :
    ∃ v : quotientAnnihilatorImage k a, (v : k ⧸ Ideal.span {a}) ^ p = u := by
  obtain ⟨t, ht, htu⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp u.property
  obtain ⟨v, hv⟩ := principalAnnihilator_has_p_roots k p a ⟨t, ht⟩
  refine ⟨⟨Ideal.Quotient.mk (Ideal.span {a}) v, Ideal.mem_map_of_mem _ v.property⟩, ?_⟩
  rw [← map_pow, hv, htu]

/-- 商でaのp冪根は零化イデアルの像を零化する。 -/
theorem quotientAnnihilatorImage_killed_by_p_root (a r : k) (n : ℕ)
    (hr : r ^ p ^ n = a) (z : k ⧸ Ideal.span {a})
    (hz : z ∈ quotientAnnihilatorImage k a) : Ideal.Quotient.mk (Ideal.span {a}) r * z = 0 := by
  obtain ⟨t, ht, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hz
  rw [← map_mul, principalAnnihilator_killed_by_p_root k p a r n hr t ht, map_zero]

omit [PerfectRing k p] in
/-- 正のp冪根の零化元のp乗は、商の零化イデアル像へ入る。
生成元の正則性を仮定せず、割り算の誤差をイデアルへ隔離する。 -/
theorem quotient_p_root_annihilator_pow_mem (a r : k) (n : ℕ)
    (hr : r ^ p ^ (n + 1) = a) (z : k ⧸ Ideal.span {a})
    (hz : Ideal.Quotient.mk (Ideal.span {a}) r * z = 0) :
    z ^ p ∈ quotientAnnihilatorImage k a := by
  let q := Ideal.Quotient.mk (Ideal.span {a})
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hm : r * t ∈ Ideal.span {a} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
  let N := p ^ (n + 1)
  have hN : 2 ≤ N := (Fact.out : p.Prime).two_le.trans
    (Nat.le_self_pow (by omega : n + 1 ≠ 0) p)
  have hn : N - 1 + 1 = N := by omega
  let u := t - r ^ (N - 1) * c
  have hru : r * u = 0 := by
    dsimp only [u]
    rw [mul_sub, hc, ← hr]
    change r ^ N * c - r * (r ^ (N - 1) * c) = 0
    rw [← mul_assoc, ← pow_succ', hn, sub_self]
  have hau : a * u = 0 := by
    rw [← hr]
    change r ^ N * u = 0
    exact pow_mul_eq_zero_of_le (by omega : 1 ≤ N) (by simpa only [pow_one] using hru)
  have hup : u ^ p ∈ principalAnnihilator k a := by
    apply (mem_principalAnnihilator k a _).mpr
    have h := pow_mul_eq_zero_of_le (a := u) (b := a) (m := 1) (n := p)
      (Fact.out : p.Prime).one_lt.le (by simpa only [pow_one, mul_comm] using hau)
    simpa only [mul_comm] using h
  have hvanish : q ((r ^ (N - 1) * c) ^ p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [mul_pow, ← pow_mul]
    apply (Ideal.span {a}).mul_mem_right
    apply (Ideal.span {a}).pow_mem_of_pow_mem (m := N) _
      (by have hp := (Fact.out : p.Prime).two_le; nlinarith : N ≤ (N - 1) * p)
    rw [show r ^ N = a from hr]
    exact Ideal.mem_span_singleton_self a
  have he : q t ^ p = q (u ^ p) := by
    have ht : t = r ^ (N - 1) * c + u := by dsimp only [u]; ring
    rw [ht, ← map_pow, add_pow_char, map_add, hvanish, zero_add]
  rw [he]
  exact Ideal.mem_map_of_mem q hup

end SerrePositivity

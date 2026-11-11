module

public import SerrePositivity.CommutativeAlgebra.Adic.Principal
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# 主元剰余からの正則性の持ち上げ

## 概要
a 進分離な環で、a と mod a の b が正則なら b も正則。

## 方針
b で消える元を a で繰り返し割り、分離性を適用する。

## 規約
Noether 性は仮定しない。

## 使われ方
BS 著者版 Construction 6.1 の A/d が p 正則な場合の A の p 正則性。
-/

public noncomputable section

namespace SerrePositivity

variable {R : Type*} [CommRing R]

/-- 概要：主元剰余の正則性を分離な係数環へ持ち上げる。
方針：b の核は a で割れることを繰り返し、a 進分離性を使う。
規約：a 自身の正則性も明示的に仮定する。
使われ方：BS 著者版 Construction 6.1 の p ねじれなしの入力。 -/
theorem isSMulRegular_of_quotient_of_isHausdorff (a b : R)
    [IsHausdorff (Ideal.span {a}) R] (ha : IsSMulRegular R a)
    (hb : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)) :
    IsSMulRegular R b := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  change b * x = 0 at hx
  have hdiv (y : R) (hy : b * y = 0) : ∃ z : R, y = a * z ∧ b * z = 0 := by
    have hq : Ideal.Quotient.mk (Ideal.span {a}) y = 0 := by
      apply hb
      change Ideal.Quotient.mk _ b * Ideal.Quotient.mk _ y = _
      simpa only [← map_mul, hy, map_zero, smul_zero]
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hq)
    refine ⟨z, hz, ?_⟩
    apply ha
    change a * (b * z) = a * 0
    rw [mul_zero, ← mul_assoc, mul_comm a b, mul_assoc, ← hz, hy]
  have hpow : ∀ n : ℕ, ∃ z : R, x = a ^ n * z ∧ b * z = 0 := by
    intro n
    induction n with
    | zero => exact ⟨x, by simp, hx⟩
    | succ n ih =>
      obtain ⟨y, hy, hby⟩ := ih
      obtain ⟨z, hz, hbz⟩ := hdiv y hby
      refine ⟨z, ?_, hbz⟩
      rw [hy, hz, pow_succ, mul_assoc]
  apply IsHausdorff.haus' (I := Ideal.span {a})
  intro n
  apply SModEq.zero.mpr
  obtain ⟨z, hz, _⟩ := hpow n
  exact (mem_principal_pow_smul_top a n x).mpr ⟨z, by simpa only [smul_eq_mul] using hz.symm⟩

end SerrePositivity

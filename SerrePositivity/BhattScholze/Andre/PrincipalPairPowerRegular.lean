module

public import SerrePositivity.BhattScholze.Andre.RegularTripleQuotientStep
public import SerrePositivity.CommutativeAlgebra.AdicCompletionRegular

/-!
# André E1・E2：正則対の主冪商と第一完備化

## 概要

b が正則で c が mod b で正則なら、c は全ての mod bⁿ と b 完備化で正則。
BS Rem 7.15（著者版 p.62）の正則対を完備化へ移すための一般環計算。

## 方針

c 倍が bⁿ で割り切れることから元の bⁿ 可除性を帰納し、完備化の各座標へ適用する。

## 規約

Noether 性・平坦性・b 完備性は要求しない。導来二座標完備化との比較は別工程。

## 使われ方

一元 raw 包の正則対から、その p 完備化における分母正則性を得る。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (b c : R) (hb : IsSMulRegular R b)
variable (hc : IsSMulRegular (R ⧸ Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) c))
include hb hc

/-- 概要：正則対の第一元の冪イデアルは第二元で飽和している。
方針：mod b で一度消去し、第一元の正則性で b を消して帰納する。
規約：零乗も含める。
使われ方：BS Rem 7.15（著者版 p.62）の全主冪商での分母正則性。 -/
theorem principalPairPower_saturated (n : ℕ) (x : R)
    (hx : c * x ∈ Ideal.span {b ^ n}) : x ∈ Ideal.span {b ^ n} := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hmod : Ideal.Quotient.mk (Ideal.span {b}) x = 0 := by
      apply hc
      change Ideal.Quotient.mk (Ideal.span {b}) c *
        Ideal.Quotient.mk (Ideal.span {b}) x = _ * 0
      rw [mul_zero, ← map_mul]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hx' : b ∣ c * x := by
        exact (dvd_pow_self b (by omega : n + 1 ≠ 0)).trans
          (Ideal.mem_span_singleton.mp hx)
      exact Ideal.mem_span_singleton.mpr hx'
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hmod)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hx
    have hcy : c * y = b ^ n * z := by
      apply hb
      change b * (c * y) = b * (b ^ n * z)
      simpa only [hy, pow_succ', mul_assoc, mul_left_comm] using hz
    have hym : y ∈ Ideal.span {b ^ n} := ih y (by
      rw [hcy]
      exact Ideal.mem_span_singleton.mpr ⟨z, rfl⟩)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hym
    apply Ideal.mem_span_singleton.mpr
    refine ⟨w, ?_⟩
    simp only [hy, hw, pow_succ', mul_assoc]

/-- 概要：正則対の第二元は第一元の任意の主冪商で正則。
方針：第一元の冪イデアルの飽和性を代表元に適用する。
規約：商上の第二元の像をスカラーとする。
使われ方：BS Rem 7.15（著者版 p.62）の古典的主完備化の座標計算。 -/
theorem principalPairPower_quotient_regular (n : ℕ) :
    IsSMulRegular (R ⧸ Ideal.span {b ^ n}) (Ideal.Quotient.mk (Ideal.span {b ^ n}) c) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply principalPairPower_saturated b c hb hc n t
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul, smul_eq_mul] using hx

/-- 概要：正則対の第二元は第一元の古典的完備化でも正則。
方針：全ての主冪商で消去し、完備化の座標の単射性を使う。
規約：元の環の完備性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の反復完備化の第一段。 -/
theorem principalPair_adicCompletion_second_regular :
    IsSMulRegular (AdicCompletion (Ideal.span {b}) R)
      (algebraMap R (AdicCompletion (Ideal.span {b}) R) c) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  apply AdicCompletion.ext_evalₐ
  intro n
  have hreg : IsSMulRegular (R ⧸ (Ideal.span {b}) ^ n)
      (Ideal.Quotient.mk ((Ideal.span {b}) ^ n) c) := by
    rw [Ideal.span_singleton_pow]
    exact principalPairPower_quotient_regular b c hb hc n
  apply hreg
  change Ideal.Quotient.mk ((Ideal.span {b}) ^ n) c *
    AdicCompletion.evalₐ (Ideal.span {b}) n x = _ * _
  simpa only [map_zero, map_mul, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AdicCompletion.evalₐ_of, smul_eq_mul, mul_zero] using
    congrArg (AdicCompletion.evalₐ (Ideal.span {b}) n) hx

end SerrePositivity.BhattScholze.Andre

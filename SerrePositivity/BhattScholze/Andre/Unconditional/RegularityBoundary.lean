module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiRegular
public import SerrePositivity.BhattScholze.Delta.DistinguishedPowerTorsion

/-!
# hpR の正則性計算における境界

## 概要
BS Rem 7.15（著者版 p.62）の生成元・ϖ 持上げの mod p 正則性は、
完全 prism の商の p 正則性と同値である。

## 方針
正則対の順序交換を両向きに使う。ϖ 持上げには x^p=d modulo p を使う。
有界ねじれは無条件に供給するが、正則性への強化はしない。

## 規約
原典は基底変更で p ねじれなしの場合へ帰着している。
一般の perfectoid 商で hpR が自動的に成立するという主張はしない。

## 使われ方
hpR を外せる分冪降下と、正則性自体を主張する既存補題を区別する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 概要：完全 prism の生成元の mod p 正則性は商の p 正則性と同値。
方針：完全 δ 環の p 正則性を使って、既存の順序交換を逆向きにも適用する。
規約：有界 p ねじれだけでこの同値の右辺を得たとは扱わない。
使われ方：BS Rem 7.15（著者版 p.62）の hpR を保持する正則性補題の判定。 -/
theorem perfectPrism_generator_modPrime_regular_iff
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) :
    IsSMulRegular (A ⧸ Ideal.span {(p : A)})
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) W.generator) ↔
      IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal) := by
  constructor
  · intro hd
    have ht := principal_regular_swap (p : A) W.generator hW.p_mul_injective hd
    simpa only [OrientedPrism.ideal, map_natCast] using ht
  · exact perfectPrism_generator_modPrime_regular W

/-- 概要：ϖ 持上げの mod p 正則性も商の p 正則性と同値。
方針：x^p=d modulo p と正の冪の正則性の同値を、生成元の判定へ渡す。
規約：零環も含み、prism 商の追加仮定を導入しない。
使われ方：BS Rem 7.15（著者版 p.62）の旧正則係数降下の必要条件を明示する。 -/
theorem perfectPrismVarpiLift_modPrime_regular_iff
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) :
    IsSMulRegular (A ⧸ Ideal.span {(p : A)})
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)) ↔
      IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal) := by
  constructor
  · intro hx
    apply (perfectPrism_generator_modPrime_regular_iff W hW).mp
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {(p : A)}))
      (perfectPrismVarpiLift_frobenius W hW)
    rw [W.deltaStructure.frobeniusLift_apply, map_add, map_pow, map_mul] at h
    simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : A)),
      zero_mul, add_zero] at h
    rw [← h]
    exact hx.pow p
  · exact perfectPrismVarpiLift_modPrime_regular W hW

/-- 概要：完全 prism の任意生成元冪商の p 冪ねじれは既定の冪で消える。
方針：完全性・生成元の distinguished 性と正則性を既存の冪ねじれ定理へ供給する。
規約：hpR を仮定せず、p 正則性とは区別する。
使われ方：BS Rem 7.15（著者版 p.62）の完備化比較に使える無条件の弱い入力。 -/
theorem perfectPrism_generator_power_bounded_torsion_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (n N : ℕ) (x : A ⧸ Ideal.span {W.generator ^ n})
    (hx : (p : A ⧸ Ideal.span {W.generator ^ n}) ^ N * x = 0) :
    (p : A ⧸ Ideal.span {W.generator ^ n}) ^ n * x = 0 := by
  let := W.isAdicComplete_p_of_perfect hW
  exact hW.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
    (W.isDistinguished_of_perfect hW) n N x hx

omit [Fact p.Prime] in
/-- 概要：非零な標数 p 環では p の乗算は単射でない。
方針：1 と 0 の像が一致することを単射性に渡す。
規約：有界 p ねじれ・被約性から hpR は従わないことを説明するための一般補題。
使われ方：BS Rem 7.15（著者版 p.62）の基底変更前の正則性を誤って仮定しないための境界。 -/
theorem not_prime_regular_of_charP (R : Type u) [CommRing R] [Nontrivial R]
    [CharP R p] : ¬ IsSMulRegular R (p : R) := by
  intro hp
  exact one_ne_zero (hp (by simp only [CharP.cast_eq_zero R p, smul_eq_mul, zero_mul]))

end SerrePositivity.BhattScholze.Andre

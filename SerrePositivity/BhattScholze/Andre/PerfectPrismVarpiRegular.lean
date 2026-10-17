module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpi
public import SerrePositivity.BhattScholze.Andre.PowerRootCoefficientPDRegularReduction
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# André E1・E2：ϖ の持上げの mod p 正則性

## 概要

完全 prism (A,(d)) の商 R が p 正則なら、x=φ⁻¹(d) の mod p 像は正則。
BS Rem 7.15（著者版 p.62）の p ねじれなしの場合の係数還元を具体化する。

## 方針

d の正則性と R の p 正則性から正則列の二元の順序を交換する。
mod p で x^p=d なので、正の冪から x 自身の正則性が従う。

## 規約

R の p 正則性を明示仮定とする。一般の perfectoid 基底へこの仮定を追加しない。

## 使われ方

既存の正則係数元による実分冪降下に、原典の ϖ の持上げを供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A]

/-- 概要：a が正則で、b が A/(a) で正則なら、a は A/(b) で正則。
方針：ac=be を mod a で調べ e=at とし、a を消去する。
規約：完備性や局所性は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の d と p の順序交換。 -/
theorem principal_regular_swap (a b : A) (ha : IsSMulRegular A a)
    (hb : IsSMulRegular (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)) :
    IsSMulRegular (A ⧸ Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) a) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro c hc
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  change Ideal.Quotient.mk _ a * Ideal.Quotient.mk _ c = 0 at hc
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hc
  obtain ⟨e, he⟩ := hc
  have he0 : Ideal.Quotient.mk (Ideal.span {a}) b * Ideal.Quotient.mk _ e = 0 := by
    rw [← map_mul, ← he, map_mul]
    simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a),
      zero_mul]
  have he' : Ideal.Quotient.mk (Ideal.span {a}) e = 0 :=
    hb (by simpa only [smul_eq_mul, mul_zero] using he0)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he')
  have hct : c = b * t := ha (by change a * c = a * (b * t); rw [he, ht]; ring)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr ⟨t, hct⟩

variable {p : ℕ} [Fact p.Prime]

/-- 概要：p 正則な prism 商を持つ完全 prism の生成元は mod p でも正則。
方針：prism 生成元の正則性と商の p 正則性の順序を交換する。
規約：仮定は R=A/(d) 上の p の単射性。
使われ方：BS Rem 7.15（著者版 p.62）の ϖ の mod p 正則性への入力。 -/
theorem perfectPrism_generator_modPrime_regular (W : OrientedPrism p A)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) :
    IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) W.generator) := by
  apply principal_regular_swap W.generator (p : A) W.generator_regular
  simpa only [OrientedPrism.ideal, map_natCast] using hpR

/-- 概要：選んだ ϖ の持上げは mod p で正則。
方針：mod p の x^p=d と正の冪の正則性判定を使う。
規約：p 正則性は prism 商に要求する。
使われ方：BS Rem 7.15（著者版 p.62）の係数還元における分冪安定性。 -/
theorem perfectPrismVarpiLift_modPrime_regular (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) :
    IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)) := by
  apply (IsSMulRegular.pow_iff (Nat.Prime.pos (Fact.out : p.Prime))).mp
  have h := congrArg (Ideal.Quotient.mk (Ideal.span {(p : A)}))
    (perfectPrismVarpiLift_frobenius W hW)
  rw [W.deltaStructure.frobeniusLift_apply, map_add, map_pow, map_mul] at h
  simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : A)),
    zero_mul, add_zero] at h
  rw [h]
  exact perfectPrism_generator_modPrime_regular W hpR

local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "D" f => PowerRootCoefficientPDEnvelope p f
local notation "z" f => powerRootCoefficientPDInput p f
local notation "J" f => principalDPPositiveIdeal (z f)

/-- 概要：原典の ϖ の持上げで還元した無限根 pd 包に実分冪構造を与える。
方針：mod p 正則性を導き、正則係数元による既存の降下を適用する。
規約：prism 商の p 正則性と f のモニック性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の R/ϖ への係数変更。 -/
def perfectPrismVarpiPowerRootDividedPowers
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
    (f : Polynomial A) (hf : f.Monic) :
    DividedPowers ((J f).map
      (Ideal.Quotient.mk (Ideal.span {(algebraMap R₀ (D f)
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)))}))) :=
  powerRootCoefficientPDRegularReduction p W hW f hf
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))
    (perfectPrismVarpiLift_modPrime_regular W hW hpR)

/-- 概要：ϖ 還元後の入力元の分冪は標準分冪生成元の商像。
方針：一般正則係数還元の計算公式を具体的な持上げに適用する。
規約：全次数を含み、還元前と同じ入力元を使う。
使われ方：BS Rem 7.15（著者版 p.62）の pd 普遍射の照合。 -/
theorem perfectPrismVarpiPowerRootDividedPowers_base_apply
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
    (f : Polynomial A) (hf : f.Monic) (n : ℕ) :
    (perfectPrismVarpiPowerRootDividedPowers W hW hpR f hf).dpow n
      (Ideal.Quotient.mk _ (algebraMap
        (PowerRootPolynomial R₀ p (Nat.Prime.pos (Fact.out : p.Prime))) (D f) (z f))) =
      Ideal.Quotient.mk _ (principalDPGenerator (z f) n) := by
  unfold perfectPrismVarpiPowerRootDividedPowers
  exact powerRootCoefficientPDRegularReduction_base_apply p W hW f hf
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))
    (perfectPrismVarpiLift_modPrime_regular W hW hpR) n

/-- 概要：ϖ の持上げによる商への標準射は分冪を保つ。
方針：一般正則係数還元の分冪射の定理を使う。
規約：分冪イデアルは正次数イデアルの実商像。
使われ方：BS Rem 7.15（著者版 p.62）の係数還元の構造射。 -/
theorem perfectPrismVarpiPowerRootDividedPowers_isDPMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
    (f : Polynomial A) (hf : f.Monic) :
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (perfectPrismVarpiPowerRootDividedPowers W hW hpR f hf)
      (Ideal.Quotient.mk (Ideal.span {(algebraMap R₀ (D f)
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)))})) := by
  unfold perfectPrismVarpiPowerRootDividedPowers
  exact powerRootCoefficientPDRegularReduction_isDPMorphism p W hW f hf
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))
    (perfectPrismVarpiLift_modPrime_regular W hW hpR)

end SerrePositivity.BhattScholze.Andre

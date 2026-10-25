module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootCoefficientIdealQuotient
public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionFiniteModPrimeRegularity
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootMonicModPrimePDEnvelope
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismVarpiRegular
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient

/-!
# André E1・E2：無限根モニック入力の mod(p,d) 正則性

## 概要

モニック入力は任意の係数イデアル商後も正則。
prism 商が p 正則なら、無限根入力の mod p で d とモニック入力は正則対となる。
BS Rem 7.15（著者版 p.62）の p ねじれなしの場合の有限関係商への入力。

## 方針

係数イデアル商との交換とモニック入力の正則性を使い、
p,d の正則性を平坦な無限根環へ移す。

## 規約

prism 商の p 正則性は明示仮定。一般の根付き存在定理へ追加しない。

## 使われ方

有限 raw δ 関係商の p 正則性と mod p の d 正則性の同時帰納法の初期値。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) (hp : 0 < p)
local notation "P" => PowerRootPolynomial A p hp

/-- 概要：任意の係数イデアル商後も無限根モニック入力は正則。
方針：係数商同型で商係数上のモニック入力の正則性へ移す。
規約：係数イデアル I の正則性や主性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の mod(p,d) 正則入力。 -/
theorem powerRootPolynomial_monic_mod_ideal_regular (I : Ideal A)
    (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular (P ⧸ I.map (algebraMap A P))
      (Ideal.Quotient.mk (I.map (algebraMap A P)) (powerRootPolynomialBaseMap A p hp f)) := by
  let e := powerRootCoefficientIdealQuotientEquiv A p hp I
  have he : e (Ideal.Quotient.mk _ (powerRootPolynomialBaseMap A p hp f)) =
      powerRootPolynomialBaseMap (A ⧸ I) p hp (f.map (Ideal.Quotient.mk I)) := by
    rw [powerRootCoefficientIdealQuotientEquiv_mk, powerRootCoefficientIdealQuotientMap_baseMap]
  have hr := powerRootPolynomial_monic_regular (A ⧸ I) p hp
    (f.map (Ideal.Quotient.mk I)) (hf.map _)
  intro x z hxz
  apply e.injective
  apply hr
  simpa only [smul_eq_mul, map_mul, he] using congrArg e hxz

/-- 概要：無限根入力の実二元係数商でモニック入力は正則。
方針：(p,d) の像を二元生成イデアルと同定する。
規約：d は任意の係数元。
使われ方：BS Rem 7.15（著者版 p.62）の有限源の初期正則対。 -/
theorem powerRootPolynomial_monic_mod_pair_regular (d : A)
    (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular (P ⧸ Ideal.span {(p : P), algebraMap A P d})
      (Ideal.Quotient.mk (Ideal.span {(p : P), algebraMap A P d})
        (powerRootPolynomialBaseMap A p hp f)) := by
  have he : (Ideal.span {(p : A), d}).map (algebraMap A P) =
      Ideal.span {(p : P), algebraMap A P d} := by
    rw [Ideal.map_span, Set.image_pair, map_natCast]
  rw [← he]
  exact powerRootPolynomial_monic_mod_ideal_regular p hp _ f hf

variable [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "Pp" => PowerRootPolynomial A p (Nat.Prime.pos (Fact.out : p.Prime))
local notation "dP" => algebraMap A Pp W.generator

include hW in
/-- 概要：p 正則な prism 商では無限根入力の d の mod p 像も正則。
方針：係数上の d の mod p 正則性を無限根環の自由性で移す。
規約：prism 商 R の p 正則性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の有限 δ 関係商の初期値。 -/
theorem powerRootPrismGenerator_modPrime_regular
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) :
    IsSMulRegular (Pp ⧸ Ideal.span {(p : Pp)})
      (Ideal.Quotient.mk (Ideal.span {(p : Pp)}) dP) := by
  have h := SerrePositivity.isSMulRegular_mod_of_flat (S := Pp) (p : A) W.generator
    hW.p_mul_injective (perfectPrism_generator_modPrime_regular W hpR)
  have aux (c : Pp) (hc : c = (p : Pp))
      (hr : IsSMulRegular (Pp ⧸ Ideal.span {c}) (Ideal.Quotient.mk (Ideal.span {c}) dP)) :
      IsSMulRegular (Pp ⧸ Ideal.span {(p : Pp)})
        (Ideal.Quotient.mk (Ideal.span {(p : Pp)}) dP) := by
    subst c
    exact hr
  exact aux _ (map_natCast (algebraMap A Pp) p) h

/-- 概要：無限根モニック入力は mod p の後に d を課した実二重商で正則。
方針：二重商同型で一重の (p,d) 商のモニック正則性を戻す。
規約：この入力自体には prism 商の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の初期線形除算関係の正則対。 -/
theorem powerRootPrismMonic_modPrime_generator_regular (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular ((Pp ⧸ Ideal.span {(p : Pp)}) ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : Pp)}) dP})
      (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : Pp)}) dP})
        (Ideal.Quotient.mk (Ideal.span {(p : Pp)}) (powerRootMonicPDInput p f))) := by
  let e := principalDoubleQuotEquiv (p : Pp) dP
  have h := powerRootPolynomial_monic_mod_pair_regular p (Nat.Prime.pos (Fact.out : p.Prime))
    W.generator f hf
  intro x z hxz
  apply e.injective
  apply h
  unfold powerRootMonicPDInput at hxz
  have he := principalDoubleQuotEquiv_mk (p : Pp) dP (powerRootPolynomialBaseMap A p
    (Nat.Prime.pos (Fact.out : p.Prime)) f)
  change e (Ideal.Quotient.mk _ (Ideal.Quotient.mk _
    (powerRootPolynomialBaseMap A p (Nat.Prime.pos (Fact.out : p.Prime)) f))) = _ at he
  simpa only [smul_eq_mul, map_mul, he] using congrArg e hxz

include hW in
/-- 概要：最初の mod p 線形除算関係は無限根モニック入力でも正則。
方針：d の mod p 正則性を最高係数の正則性判定へ渡す。
規約：変数族 τ は任意で、prism 商の p 正則性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の最初の有限関係商の p 正則性への入力。 -/
theorem powerRootPrismFirstModPrimeRelation_regular
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
    (f : Polynomial A) {τ : Type v} (s : τ) :
    IsSMulRegular (MvPolynomial τ (Pp ⧸ Ideal.span {(p : Pp)}))
      (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {(p : Pp)}) dP) * MvPolynomial.X s -
        MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {(p : Pp)})
          (powerRootMonicPDInput p f))) := by
  simpa only [map_neg, sub_eq_add_neg] using
    linearMvPolynomial_regular (Ideal.Quotient.mk (Ideal.span {(p : Pp)}) dP)
      (-(Ideal.Quotient.mk (Ideal.span {(p : Pp)}) (powerRootMonicPDInput p f))) s
      (powerRootPrismGenerator_modPrime_regular p W hW hpR)

include hW in
/-- 概要：最初の mod p 線形除算関係を課しても prism 生成元の係数像は正則。
方針：モニック入力の mod(p,d) 正則性と線形関係の正則対の順序交換を使う。
規約：prism 商の p 正則性とモニック性のみを要求する。
使われ方：BS Rem 7.15（著者版 p.62）の有限関係商の同時帰納法の初期値。 -/
theorem powerRootPrismMonicFirstModPrime_generator_regular
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
    (f : Polynomial A) (hf : f.Monic) {τ : Type v} (s : τ) :
    let R₀ := Pp ⧸ Ideal.span {(p : Pp)}
    let g : MvPolynomial τ R₀ :=
      MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {(p : Pp)}) dP) * MvPolynomial.X s -
        MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {(p : Pp)}) (powerRootMonicPDInput p f))
    IsSMulRegular (MvPolynomial τ R₀ ⧸ Ideal.span {g})
      (Ideal.Quotient.mk (Ideal.span {g})
        (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {(p : Pp)}) dP))) := by
  exact linearMvPolynomial_coefficient_regular_quotient _ _ s
    (powerRootPrismGenerator_modPrime_regular p W hW hpR)
    (powerRootPrismMonic_modPrime_generator_regular p W f hf)

end SerrePositivity.BhattScholze.Andre

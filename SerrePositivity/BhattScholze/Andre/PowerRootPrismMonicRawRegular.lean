module

public import SerrePositivity.BhattScholze.Andre.DeltaDivisionUnaryRawRegular
public import SerrePositivity.BhattScholze.Andre.PowerRootMonicModPairRegular
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicCompletionPD

/-!
# André R1：無限根モニック raw 包の有限段の条件付き正則対

## 概要

p 正則な prism 商を持つ完全 prism 上で、全有限段の p と mod p の生成元は正則。
BS Rem 7.15（著者版 p.62）の p ねじれなしの場合の源の計算。

## 方針

prism の正則対とモニック入力の mod(p,d) 正則性を一般有限段帰納法へ供給する。

## 規約

prism 商の p 正則性を明示する。raw 包をねじれ除去商に変更しない。
実完備化への保存と prismatic 源の同定は別工程。

## 使われ方

全有限段の条件付き計算と一元自由 δ 環の型を提供する。
raw 全体の p 正則性は不要になった hpR 付き宣言を削除し、
Unconditional.RawPrimeRegularAllMonic の実源の純性による証明を正本とする。
この置換先は原典と異なる局所化・導来完備化の純性を使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
/-- 概要：無限根入力の同じ宇宙の一元自由 δ 環の台環を固定する。
方針：一元添字型を宇宙付きで定義する。
規約：入力族と自由環で同じ添字型を使う。
使われ方：BS Rem 7.15（著者版 p.62）の具体的 ghost 単射性の入力。 -/
abbrev PowerRootUnaryFreeDeltaRing (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p) :=
  RelativeFreeDeltaRing (R := PowerRootPolynomial A p hp) PUnit.{u + 1}

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "I" => deltaDivisionFiniteRelationIdeal E dP a
local notation "Raw" => DeltaAdjoinDivision E dP a

include hpR hf in
/-- 概要：無限根モニック入力の全有限段で p と mod p の生成元は正則。
方針：モニック正則性・prism の正則対・ghost 単射性を内部で供給して帰納する。
規約：正次数は不要で、prism 商の p 正則性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の raw 包の p 正則性の具体的入力。 -/
theorem powerRootPrismMonicFinite_all_regular (N : ℕ) :
    let B := L₀ ⧸ I N
    IsSMulRegular B (p : B) ∧ IsSMulRegular (B ⧸ Ideal.span {(p : B)})
      (Ideal.Quotient.mk (Ideal.span {(p : B)}) (Ideal.Quotient.mk (I N) (MvPolynomial.C dP))) := by
  have hpP := powerRootPolynomial_primeRegular p hW.p_mul_injective
  have hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀) := by
    apply witt_ghostMap_injective_of_mul_prime_injective
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular P (p : P) from hpP).of_flat (S := L₀)
  let v := (powerRootPrismGenerator_isDistinguished W hW).unit
  have hv : (v : P) = (E).delta dP :=
    (powerRootPrismGenerator_isDistinguished W hW).unit_spec
  exact deltaDivisionUnaryFinite_all_regular E dP a hpP
    (powerRootPrismGenerator_modPrime_regular p W hW hpR)
    (powerRootPrismMonic_modPrime_generator_regular p W f hf) hgL v hv N

end SerrePositivity.BhattScholze.Andre

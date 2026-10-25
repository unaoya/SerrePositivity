module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionUnaryRawPairRegular
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicRawRegular
public import SerrePositivity.BhattScholze.Andre.Remark715.PrincipalPairCompletionRegular
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PrimeReductionPurity
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.RawPAdicPairRegular

/-!
# André E1・E2：無限根モニック raw 包の正則対

## 概要

p 正則な prism 商を持つ完全 prism 上の無限根モニック raw 包で、p と mod p の分母は正則。
BS Rem 7.15（著者版 p.62）の実完備化前の計算。

## 方針

有限段の分母正則性を実 δ 閉包商の mod p に移す一般結果へ、prism とモニック性を供給する。

## 規約

正次数は要求しない。raw と mod p の中間主張では prism 商の p 正則性を明示する。
通常 p 完備化の正則対と実二座標完備化の分母正則性にはこの仮定を要求しない。
通常 p 完備化の旧宣言は削除し、実源の純性と標準 H⁰ 比較による
Unconditional.RawPAdicPairRegular の公開名を使う。原典とは異なる証明経路。

## 使われ方

元の raw 包の実完備化への正則対保存の入力。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
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
local notation "Raw" => DeltaAdjoinDivision E dP a

include hpR hf in
/-- 概要：無限根モニック raw 包の mod p で prism 生成元の像は正則。
方針：prism 正則対とモニック入力を供給し、有向上限で得た分母飽和性を使う。
規約：元の δ 閉包商を使い、正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化前の正則対の第二成分。 -/
theorem powerRootPrismMonicRaw_mod_prime_generator_regular :
    IsSMulRegular (Raw ⧸ Ideal.span {(p : Raw)})
      (Ideal.Quotient.mk (Ideal.span {(p : Raw)}) (deltaAdjoinDivisionMap E dP a dP)) := by
  have hpP := powerRootPolynomial_primeRegular p hW.p_mul_injective
  have hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀) := by
    apply witt_ghostMap_injective_of_mul_prime_injective
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular P (p : P) from hpP).of_flat (S := L₀)
  let v := (powerRootPrismGenerator_isDistinguished W hW).unit
  have hv : (v : P) = (E).delta dP :=
    (powerRootPrismGenerator_isDistinguished W hW).unit_spec
  exact deltaDivisionUnaryRaw_mod_prime_d_regular E dP a hpP
    (powerRootPrismGenerator_modPrime_regular p W hW hpR)
    (powerRootPrismMonic_modPrime_generator_regular p W f hf) hgL v hv

include hf in
/-- 概要：無限根モニック raw 包の実二座標完備化 H⁰ で分母の像は正則。
方針：A1-b の実源の純性と次数零モニック入力の零環性から得た正則性を使う。
原典の p ねじれなしへの帰着とは異なる純性による経路。
規約：元の Koszul 完備化 H⁰ と標準射を保持し、hpR・正次数を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化の分母ねじれの排除。 -/
theorem powerRootPrismMonicRaw_pdCompletion_generator_regular :
    let dL := deltaAdjoinDivisionMap E dP a dP
    letI := SerrePositivity.DerivedCompletion.pdCompletionCommRing Raw p dL
    IsSMulRegular (SerrePositivity.DerivedCompletion.PDCompletionH0 Raw p dL)
      (SerrePositivity.DerivedCompletion.pdCompletionUnit Raw p dL dL) := by
  exact powerRootPrismMonicRaw_pdCompletion_generator_regular_of_monic_unconditional W hW f hf

end SerrePositivity.BhattScholze.Andre

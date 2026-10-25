module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicHodgeTateVarpiFlat
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatPowerTorsion

/-!
# André R1：Hodge–Tate 商の条件付き ϖ 正則性

## 概要

prism 商が p 正則なら、元のモニック Hodge–Tate 商でも ϖ が正則。
BS Rem 7.15（著者版 p.62）の条件付きの中間計算。

## 方針

(ϖ^p)=(p) と条件付きの商の p 正則性から ϖ 正則性を得る。

## 規約

この正則性は一般には無条件化できない。旧完全平坦性の2定理は不要となったので削除し、
完全忠実平坦性の呼出しは A1-b の実源の純性による無条件版へ移した。

## 使われ方

A1-c2 の既存の条件付き係数比較が使う正則性を、最終比較が届くまで保持する。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion

/-- 概要：正則元と同じ主イデアルを生成する正冪の底も正則。
方針：主イデアル所属による可除性と積・正冪の正則性を使う。
規約：零環も含める。
使われ方：BS Rem 7.15（著者版 p.62）の (ϖ^p)=(p) からの正則性。 -/
theorem regular_of_span_power_eq {B : Type u} [CommRing B] (b c : B) (n : ℕ)
    (hn : 0 < n) (he : Ideal.span {b ^ n} = Ideal.span {c}) (hc : IsSMulRegular B c) :
    IsSMulRegular B b := by
  have hm : c ∈ Ideal.span {b ^ n} := by rw [he]; exact Ideal.mem_span_singleton_self c
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hm
  rw [hz, mul_comm] at hc
  exact (IsSMulRegular.pow_iff hn).mp hc.of_mul

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
variable (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f

include hpR hf in
/-- 概要：自然な Hodge–Tate 候補で基底の ϖ は正則に作用する。
方針：基底の主イデアル等式を自然な基底射で移し、候補の p 正則性を使う。
規約：正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の完全平坦性の正則性条件。 -/
theorem powerRootPrismMonicHodgeTate_varpi_regular :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    IsSMulRegular T v := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  have he : Ideal.span {(φ v) ^ p} = Ideal.span {(p : T)} := by
    simpa only [Ideal.map_span, Set.image_singleton, map_pow, map_natCast] using
      congrArg (Ideal.map φ) (perfectPrismVarpi_span_pow W hW)
  have h := regular_of_span_power_eq (φ v) (p : T) p hp he
    (powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular W hW hpR f hf)
  exact h

end SerrePositivity.BhattScholze.Andre

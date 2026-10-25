module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionCompletionPrincipalPD
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismFrobeniusResidue
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootMonicModPrimePDEnvelope
public import SerrePositivity.CommutativeAlgebra.WittGhostInjective

/-!
# André E1・E2：無限根モニック入力の実完備化剰余と pd 表示

## 概要

完全 prism 上の無限根多項式環で、モニック入力の raw 包の実完備化を
prism 生成元と ϖ の持上げで割ると、係数二元商上の主分冪表示と環同型。
BS Rem 7.15（著者版 p.62）の一元モニック入力への具体的適用。

## 方針

完全 prism とモニック性から一般比較に必要な正則性・局所性・単元を全て供給する。

## 規約

入力の正次数、prism 商の p 正則性を仮定しない。実 prismatic 源の同定は別工程。
原典とは異なる Witt 座標と階乗表示による証明を用いる。

## 使われ方

原典の R/ϖ 上の実 pd 包への係数環比較に渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "hE" => powerRootPolynomialDelta_isPerfect p W.deltaStructure hW
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)

/-- 概要：無限根入力の δ 構造でも自然数 p は distinguished。
方針：係数 prism の p 完備性による単元 δ(p) を標準係数 δ 射で送る。
規約：無限根多項式環そのものの完備性は仮定しない。
使われ方：BS Cor 2.39（著者版 p.25）、Rem 7.15（p.62）の階乗比較の入力。 -/
theorem powerRootPrismPrime_isDistinguished : (E).IsDistinguished (p : P) := by
  let := W.isAdicComplete_p_of_perfect hW
  have hdp := DeltaStructure.isDistinguished_p W.deltaStructure
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))
  have hunit := hdp.map (algebraMap A P)
  have hδ := powerRootPolynomialDelta_coeff_isDeltaHom p hW.p_mul_injective
    W.deltaStructure (p : A)
  rw [hδ] at hunit
  simpa only [map_natCast, DeltaStructure.IsDistinguished] using hunit

variable (f : Polynomial A) (hf : f.Monic)
local notation "y" => powerRootMonicPDInput p f
/-- 概要：モニック無限根入力を同じ宇宙の一元族として固定する。
方針：一元添字型上の定数関数を使う。
規約：全ての適用で同じ添字型を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の一元 raw 比較の宇宙照合。 -/
abbrev powerRootPrismMonicUnaryFamily : PUnit.{u + 1} → P := fun _ => y
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "K" => Ideal.span {(p : P), dP}
local notation "Q" => P ⧸ K
local notation "bar" => Ideal.Quotient.mk K

/-- 概要：無限根モニック raw 包の実完備化剰余は係数二元商上の主分冪表示と環同型。
方針：一般実完備化比較へ完全 prism の正則性とモニック入力の mod p 正則性を供給する。
規約：補助的な正則性・ghost 単射性・分母単元を仮定に残さない。
使われ方：BS Rem 7.15（著者版 p.62）の具体的無限根 pd 台環への接続。 -/
def powerRootPrismMonicCompletionPDEquiv :
    letI := pdCompletionCommRing L p (jL dP)
    (H ⧸ Ideal.span {uL (jL dP), uL (jL xP)}) ≃+*
      PrincipalDPPresentation Q (bar y) := by
  let := pdCompletionCommRing L p (jL dP)
  have hpP := powerRootPolynomial_primeRegular p hW.p_mul_injective
  have hgP : Function.Injective (WittVector.ghostMap : WittVector p P → ℕ → P) :=
    witt_ghostMap_injective_of_mul_prime_injective p P hpP
  have hgL : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) PUnit.{u + 1}) →
        ℕ → RelativeFreeDeltaRing (R := P) PUnit.{u + 1}) := by
    apply witt_ghostMap_injective_of_mul_prime_injective
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular P (p : P) from hpP).of_flat
        (S := RelativeFreeDeltaRing (R := P) PUnit.{u + 1})
  let v := (powerRootPrismPrime_isDistinguished W hW).unit
  have hv : (v : P) = (E).delta (p : P) :=
    (powerRootPrismPrime_isDistinguished W hW).unit_spec
  have h :
      (H ⧸ Ideal.span {uL (jL dP), uL (jL (((E).frobeniusEquiv hE).symm dP))}) ≃+*
        PrincipalDPPresentation Q (bar y) := by
    with_reducible exact (deltaDivisionCompletionPrincipalPDEquiv
      (powerRootPolynomial_primeLocal p (perfectPrism_primeLocal W hW)) hpP E hE hgP hgL
      dP (powerRootPrismGenerator_isDistinguished W hW) y v hv
      (powerRootMonicPDInput_modPrime_regular p f hf))
  exact (Ideal.quotEquivOfEq (congrArg
    (fun z : P => Ideal.span {uL (jL dP), uL (jL z)})
    (powerRootPrismVarpiLift_inverseFrobenius W hW).symm)).trans h

/-- 概要：無限根入力の実完備化比較は全係数 r を φ(r) の剰余係数へ送る。
方針：一般比較の係数公式と ϖ 持上げの商の書換えを使う。
規約：r は元の係数 A に限らず無限根環 P の任意の元。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 引戻しの係数作用の照合。 -/
theorem powerRootPrismMonicCompletionPDEquiv_coeff (r : P) :
    letI := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicCompletionPDEquiv W hW f hf
        (Ideal.Quotient.mk _ (uL (jL r))) =
      algebraMap Q (PrincipalDPPresentation Q (bar y)) (bar ((E).frobeniusLift r)) := by
  let := pdCompletionCommRing L p (jL dP)
  have hpP := powerRootPolynomial_primeRegular p hW.p_mul_injective
  have hgP : Function.Injective (WittVector.ghostMap : WittVector p P → ℕ → P) :=
    witt_ghostMap_injective_of_mul_prime_injective p P hpP
  have hgL : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) PUnit.{u + 1}) →
        ℕ → RelativeFreeDeltaRing (R := P) PUnit.{u + 1}) := by
    apply witt_ghostMap_injective_of_mul_prime_injective
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular P (p : P) from hpP).of_flat
        (S := RelativeFreeDeltaRing (R := P) PUnit.{u + 1})
  let v := (powerRootPrismPrime_isDistinguished W hW).unit
  have hv : (v : P) = (E).delta (p : P) :=
    (powerRootPrismPrime_isDistinguished W hW).unit_spec
  have h := deltaDivisionCompletionPrincipalPDEquiv_coeff
    (powerRootPolynomial_primeLocal p (perfectPrism_primeLocal W hW)) hpP E hE hgP hgL
    dP (powerRootPrismGenerator_isDistinguished W hW) y v hv
    (powerRootMonicPDInput_modPrime_regular p f hf) r
  unfold powerRootPrismMonicCompletionPDEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  with_reducible exact h

end SerrePositivity.BhattScholze.Andre

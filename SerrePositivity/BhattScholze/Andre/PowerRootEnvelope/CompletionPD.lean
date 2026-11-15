module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DeltaDivisionResidue
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilies.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootInput
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Varpi
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalDP
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient

/-!
# 無限根入力の完備化剰余と pd 表示

## 概要
raw 二重剰余と Frobenius、モニック入力の完備化剰余と pd 表示、raw 包の有限段の正則対、mod (p,d) 正則性、ϖ pd 表示と ϖ 剰余の忠実平坦性、逆 Frobenius 入力を mod p 入力へ戻すこと。
BS 著者版 Remark 7.15 の φ 引き戻しの計算に使う、無限根入力の完備化剰余と分冪表示を比較する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPrism`、`PowerRootEnvelope/FrobeniusPullback`、`PowerRootEnvelope/Unconditional/Residue`、`Variants/Auxiliary`、`Variants/MonicRootedExtension`。
-/

universe u v

/-! ## 実無限根入力の raw 二重剰余と Frobenius

## 概要

完全 prism の無限根 δ 入力上で、prism 生成元の商と選択済みの ϖ の持上げの商を、
Frobenius 側の d 商と p 商へ具体的な環同型で送る。
BS 著者版 Remark 7.15（著者版 p.62）の完備化前の入力への適用。

## 方針

生成元の distinguished 性を係数 δ 射で移し、逆 Frobenius の係数公式で
無限根環内の逆像を選択済みの係数元と同定する。一般の raw 二重剰余比較を適用する。

## 規約

モニック性や prism 商の p 正則性は、この raw 比較には不要。
prismatic envelope の完備化済みの比較を含まない。

## 使われ方

原典の一元入力や任意の入力族に、補助的な distinguished 性の仮定なしで比較を供給する。
-/

@[expose] public noncomputable section PowerRootPrismFrobeniusResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "hE" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta_isPerfect p W.deltaStructure hW
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)

/-- 概要：無限根入力環内でも選択済みの ϖ の持上げは生成元の逆 Frobenius 像。
方針：係数 Frobenius との可換性と φ(x)=d を使い、Frobenius 同型で消去する。
規約：係数射は既存の標準射。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 二重剰余の正確な係数元。 -/
theorem powerRootPrismVarpiLift_inverseFrobenius :
    ((E).frobeniusEquiv hE).symm dP = xP := by
  apply ((E).frobeniusEquiv hE).injective
  rw [RingEquiv.apply_symm_apply]
  change dP = (E).frobeniusLift xP
  rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta_frobenius, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialFrobenius_coeff,
    perfectPrismVarpiLift_frobenius]

/-- 概要：prism 生成元の係数像は無限根 δ 環でも distinguished。
方針：係数 δ 射による δ 値の可換性と単元の像の単元性を使う。
規約：正則性を追加仮定にしない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二元イデアル標準化への入力。 -/
theorem powerRootPrismGenerator_isDistinguished : (E).IsDistinguished dP := by
  have hunit := (W.isDistinguished_generator).map (algebraMap A P)
  change IsUnit ((algebraMap A P) (W.deltaStructure.delta W.generator)) at hunit
  have hδ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta_coeff_isDeltaHom p hW.p_mul_injective
    W.deltaStructure W.generator
  rw [hδ] at hunit
  exact hunit

variable {σ : Type v} (a : σ → _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p (Nat.Prime.pos (Fact.out : p.Prime)))
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "j" => deltaAdjoinDivisionMap E dP a
local notation "Rawφ" => DeltaAdjoinDivision E (DeltaStructure.frobeniusLift E dP)
  (fun s => DeltaStructure.frobeniusLift E (a s))
local notation "jφ" => deltaAdjoinDivisionMap E (DeltaStructure.frobeniusLift E dP)
  (fun s => DeltaStructure.frobeniusLift E (a s))

/-- 概要：無限根入力の raw 二重商は Frobenius 側の d,p 二重商と環同型。
方針：逆 Frobenius 係数元を選択済みの ϖ の持上げへ書き換え、一般比較を適用する。
規約：入力族は任意で、生成元の distinguished 性は完全 prism から供給する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実入力上の raw 剰余比較。 -/
def powerRootPrismFrobeniusDoubleResidueEquiv :
    ((Raw ⧸ Ideal.span {j dP}) ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span {j dP}) (j xP)}) ≃+*
        ((Rawφ ⧸ Ideal.span {jφ dP}) ⧸
          Ideal.span {(p : Rawφ ⧸ Ideal.span {jφ dP})}) :=
  (Ideal.quotEquivOfEq (congrArg
    (fun t : P => Ideal.span {Ideal.Quotient.mk (Ideal.span {j dP}) (j t)})
    (powerRootPrismVarpiLift_inverseFrobenius W hW).symm)).trans
      (deltaDivisionFrobeniusDoubleResidueEquiv E dP a hE
        (powerRootPrismGenerator_isDistinguished W hW))

/-- 概要：無限根 raw 二重商の比較は任意の入力係数に標準 Frobenius を適用する。
方針：係数元の商同型と一般 raw 比較の係数公式を合成する。
規約：係数は無限根入力環 P の全ての元。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数作用を保つ後続の完備化比較。 -/
theorem powerRootPrismFrobeniusDoubleResidueEquiv_coeff (b : P) :
    powerRootPrismFrobeniusDoubleResidueEquiv W hW a
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (j b))) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (jφ ((E).frobeniusLift b))) := by
  have h := deltaDivisionFrobeniusDoubleResidueEquiv_coeff E dP a hE
    (powerRootPrismGenerator_isDistinguished W hW) b
  unfold powerRootPrismFrobeniusDoubleResidueEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact h

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismFrobeniusResidue

/-! ## 無限根モニック入力の実完備化剰余と pd 表示

## 概要

完全 prism 上の無限根多項式環で、モニック入力の raw 包の実完備化を
prism 生成元と ϖ の持上げで割ると、係数二元商上の主分冪表示と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の一元モニック入力への具体的適用。

## 方針

完全 prism とモニック性から一般比較に必要な正則性・局所性・単元を全て供給する。

## 規約

入力の正次数、prism 商の p 正則性を仮定しない。実 prismatic 源の同定は別工程。
原典とは異なる Witt 座標と階乗表示による証明を用いる。

## 使われ方

原典の R/ϖ 上の実 pd 包への係数環比較に渡す。
-/

@[expose] public noncomputable section PowerRootPrismMonicCompletionPD

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "hE" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta_isPerfect p W.deltaStructure hW
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)

/-- 概要：無限根入力の δ 構造でも自然数 p は distinguished。
方針：係数 prism の p 完備性による単元 δ(p) を標準係数 δ 射で送る。
規約：無限根多項式環そのものの完備性は仮定しない。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）、BS 著者版 Remark 7.15（p.62）の階乗比較の入力。 -/
theorem powerRootPrismPrime_isDistinguished : (E).IsDistinguished (p : P) := by
  let := W.isAdicComplete_p_of_perfect hW
  have hdp := DeltaStructure.isDistinguished_p W.deltaStructure
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))
  have hunit := hdp.map (algebraMap A P)
  have hδ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta_coeff_isDeltaHom p hW.p_mul_injective
    W.deltaStructure (p : A)
  rw [hδ] at hunit
  simpa only [map_natCast, DeltaStructure.IsDistinguished] using hunit

variable (f : Polynomial A) (hf : f.Monic)
local notation "y" => powerRootMonicPDInput p f
/-- 概要：モニック無限根入力を同じ宇宙の一元族として固定する。
方針：一元添字型上の定数関数を使う。
規約：全ての適用で同じ添字型を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一元 raw 比較の宇宙照合。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的無限根 pd 台環への接続。 -/
def powerRootPrismMonicCompletionPDEquiv :
    letI := pdCompletionCommRing L p (jL dP)
    (H ⧸ Ideal.span {uL (jL dP), uL (jL xP)}) ≃+*
      PrincipalDPPresentation Q (bar y) := by
  let := pdCompletionCommRing L p (jL dP)
  have hpP := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomial_primeRegular p hW.p_mul_injective
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 引戻しの係数作用の照合。 -/
theorem powerRootPrismMonicCompletionPDEquiv_coeff (r : P) :
    letI := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicCompletionPDEquiv W hW f hf
        (Ideal.Quotient.mk _ (uL (jL r))) =
      algebraMap Q (PrincipalDPPresentation Q (bar y)) (bar ((E).frobeniusLift r)) := by
  let := pdCompletionCommRing L p (jL dP)
  have hpP := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomial_primeRegular p hW.p_mul_injective
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

end PowerRootPrismMonicCompletionPD

/-! ## 実完備化剰余と逆 Frobenius 係数入力の ϖ pd 表示

## 概要

無限根モニック raw 包の実完備化の二元剰余を R/ϖ 上の主 pd 表示と比較する。
標準変数を固定した入力は逆 Frobenius で係数変更した多項式である。
BS 著者版 Remark 7.15（著者版 p.62）への比較で係数作用を明示する。

## 方針

(p,d) 係数の主分冪表示を逆係数 Frobenius で移し、実完備化剰余の同型に合成する。

## 規約

元の f の pd 包との同定は主張しない。prismatic 源の同定も別工程。
原典とは異なる具体的な Witt 座標と係数変更を使う。

## 使われ方

ϖ 剰余の自然な係数作用と通常忠実平坦性を検証するための比較。
-/

@[expose] public noncomputable section PowerRootPrismMonicVarpiPDComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "K" => Ideal.span {(p : P), dP}
local notation "Q" => P ⧸ K
local notation "bar" => Ideal.Quotient.mk K
local notation "y" => powerRootMonicPDInput p f
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)
local notation "f'" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp (Polynomial.map barr
  (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "C" => powerRootFrobeniusPairVarpiInputEquiv W hW

/-- 概要：二元係数商上の主分冪表示は逆 Frobenius 係数入力の ϖ 表示と環同型。
方針：入力を保つ係数環同型を主分冪表示へ持ち上げる。
規約：入力 f' の係数変更を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化比較へ合成する pd 台環同型。 -/
def powerRootPrismInverseVarpiPDEquiv : PrincipalDPPresentation Q (bar y) ≃+* Dv :=
  principalDPRingEquivOfEq C (bar y) zv (powerRootFrobeniusPairVarpiInputEquiv_input W hW f)

/-- 概要：ϖ 表示への主分冪同型は全標準生成元の次数を保つ。
方針：主分冪係数同型の生成元公式を使う。
規約：全次数 n を含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実分冪構造の比較への入力。 -/
theorem powerRootPrismInverseVarpiPDEquiv_generator (n : ℕ) :
    powerRootPrismInverseVarpiPDEquiv W hW f (principalDPGenerator (bar y) n) =
      principalDPGenerator zv n :=
  principalDPRingEquivOfEq_generator _ _ _ _ n

/-- 概要：主分冪同型は全入力係数を明示した無限根係数同型で送る。
方針：主分冪係数同型の一般公式を使う。
規約：係数は Q の全ての元。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化係数作用の合成。 -/
theorem powerRootPrismInverseVarpiPDEquiv_coeff (r : Q) :
    powerRootPrismInverseVarpiPDEquiv W hW f (algebraMap Q _ r) = algebraMap Nv Dv (C r) :=
  principalDPRingEquivOfEq_coeff _ _ _ _ r

/-- 概要：実完備化の二元剰余は逆 Frobenius 係数入力の R/ϖ 主分冪表示と環同型。
方針：実完備化の二元商比較と ϖ 係数への主分冪同型を合成する。
規約：完全 prism とモニック性のみを仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の ϖ 剰余の通常平坦性への接続。 -/
def powerRootPrismMonicVarpiCompletionPDEquiv (hf : f.Monic) :
    letI := pdCompletionCommRing L p (jL dP)
    (H ⧸ Ideal.span {uL (jL dP), uL (jL xP)}) ≃+* Dv := by
  let := pdCompletionCommRing L p (jL dP)
  exact (powerRootPrismMonicCompletionPDEquiv W hW f hf).trans
    (powerRootPrismInverseVarpiPDEquiv W hW f)

/-- 概要：実完備化比較は全無限根係数に Frobenius と明示係数比較を順に適用する。
方針：二つの環同型の係数公式を合成する。
規約：元の実完備化単位を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の変数を含む係数作用の照合。 -/
theorem powerRootPrismMonicVarpiCompletionPDEquiv_coeff (hf : f.Monic) (r : P) :
    letI := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicVarpiCompletionPDEquiv W hW f hf
        (Ideal.Quotient.mk _ (uL (jL r))) =
      algebraMap Nv Dv (C (bar ((E).frobeniusLift r))) := by
  let := pdCompletionCommRing L p (jL dP)
  rw [powerRootPrismMonicVarpiCompletionPDEquiv, RingEquiv.trans_apply,
    powerRootPrismMonicCompletionPDEquiv_coeff, powerRootPrismInverseVarpiPDEquiv_coeff]

/-- 概要：実完備化比較は元の A の係数を自然な R/ϖ 係数として保つ。
方針：Frobenius と逆係数 Frobenius の相殺と係数作用の塔を使う。
規約：逆 Frobenius 係数多項式を使った同型についての公式。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な ϖ 係数作用の確認。 -/
theorem powerRootPrismMonicVarpiCompletionPDEquiv_base_coeff (hf : f.Monic) (r : A) :
    letI := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicVarpiCompletionPDEquiv W hW f hf
        (Ideal.Quotient.mk _ (uL (jL (algebraMap A P r)))) = algebraMap Rv Dv (barr r) := by
  let := pdCompletionCommRing L p (jL dP)
  rw [powerRootPrismMonicVarpiCompletionPDEquiv_coeff, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta_frobenius,
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialFrobenius_coeff, powerRootFrobeniusPairVarpiInputEquiv_coeff]
  rw [show (W.deltaStructure.frobeniusEquiv hW).symm (W.deltaStructure.frobeniusLift r) = r from
    (W.deltaStructure.frobeniusEquiv hW).symm_apply_apply r]
  exact (IsScalarTower.algebraMap_apply Rv Nv Dv (barr r)).symm

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicVarpiPDComparison

/-! ## 実完備化の ϖ 剰余の自然な係数作用と忠実平坦性

## 概要

完全 prism 上の無限根モニック入力について、実完備化を生成元と ϖ 持上げで割った
通常環は R/ϖ 上自由であり、入力が正次数なら忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の具体的 pd 計算による通常平坦性。

## 方針

係数を逆 Frobenius で変更した実 pd 表示から係数作用と自由性を移す。
元の A 係数の完備化像と一致する公式を証明して自然な作用を確認する。

## 規約

実 prismatic 源の同定、元の f の pd 包との同定、源全体の p 正則性は別工程。
原典とは異なる入力の係数変更を明示して用いる。

## 使われ方

実完備化剰余の忠実平坦性を後続の prismatic 源との比較へ供給する。
-/

@[expose] public noncomputable section PowerRootPrismMonicVarpiFlat

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "S" => H ⧸ Ideal.span {uL (jL dP), uL (jL xP)}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)
local notation "f'" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp (Polynomial.map barr
  (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "F" => powerRootPrismMonicVarpiCompletionPDEquiv W hW f hf

/-- 概要：実完備化の ϖ 剰余に R/ϖ の係数代数構造を与える。
方針：検証済みの主 pd 同型の逆射で標準係数射を戻す。
規約：次の係数公式で元の完備化係数像との一致を確認する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常忠実平坦性の自然な係数作用。 -/
@[instance_reducible] def powerRootPrismMonicVarpiResidueAlgebra :
    letI := pdCompletionCommRing L p (jL dP)
    Algebra Rv S := by
  let := pdCompletionCommRing L p (jL dP)
  exact ((F).symm.toRingHom.comp (algebraMap Rv Dv)).toAlgebra

/-- 概要：主 pd 表示への実完備化剰余同型は R/ϖ 代数同型。
方針：逆同型で定めた係数作用に対し順逆合成の公式を使う。
規約：元の実完備化 H⁰ の通常商を維持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自由性と忠実平坦性の移送。 -/
def powerRootPrismMonicVarpiResidueAlgEquiv :
    letI := pdCompletionCommRing L p (jL dP)
    letI := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
    S ≃ₐ[Rv] Dv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
  exact { F with commutes' := fun r => (F).apply_symm_apply (algebraMap Rv Dv r) }

/-- 概要：R/ϖ の係数作用は元の A 係数の実完備化像と一致する。
方針：主 pd 同型の単射性と自然係数上の公式を使う。
規約：全ての r∈A で指定するため、作用は任意の移送として残らない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な通常係数作用の確認。 -/
theorem powerRootPrismMonicVarpiResidueAlgebra_base_coeff (r : A) :
    letI := pdCompletionCommRing L p (jL dP)
    letI := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
    algebraMap Rv S (barr r) = Ideal.Quotient.mk _ (uL (jL (algebraMap A P r))) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
  apply (F).injective
  change F ((F).symm (algebraMap Rv Dv (barr r))) = _
  rw [RingEquiv.apply_symm_apply, powerRootPrismMonicVarpiCompletionPDEquiv_base_coeff]

/-- 概要：実完備化の ϖ 剰余は自然な R/ϖ 作用で自由。
方針：逆 Frobenius 係数多項式のモニック性と pd 表示の基底を移す。
規約：入力の正次数と prism 商の p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常平坦性の具体的結論。 -/
theorem powerRootPrismMonicVarpiResidue_free :
    letI := pdCompletionCommRing L p (jL dP)
    letI := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
    Module.Free Rv S := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
  let := perfectPrismVarpiNativePDEnvelope_free W hW f'
    (perfectPrismInverseFrobeniusPolynomial_monic W hW f hf)
  exact Module.Free.of_equiv (powerRootPrismMonicVarpiResidueAlgEquiv W hW f hf).symm.toLinearEquiv

/-- 概要：正次数モニック入力の実完備化の ϖ 剰余は自然な R/ϖ 作用で忠実平坦。
方針：逆 Frobenius で次数を保存し、pd 表示の忠実平坦性を代数同型で移す。
規約：prism 商の p 正則性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化剰余からの忠実平坦性。 -/
theorem powerRootPrismMonicVarpiResidue_faithfullyFlat (hdeg : 0 < f.natDegree) :
    letI := pdCompletionCommRing L p (jL dP)
    letI := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
    Module.FaithfullyFlat Rv S := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
  have hdeg' : 0 < (f').natDegree := by
    simpa only [perfectPrismInverseFrobeniusPolynomial,
      Polynomial.natDegree_map_eq_of_injective
        (f := (W.deltaStructure.frobeniusEquiv hW).symm.toRingHom)
        (W.deltaStructure.frobeniusEquiv hW).symm.injective]
      using hdeg
  let := perfectPrismVarpiNativePDEnvelope_faithfullyFlat W hW f'
    (perfectPrismInverseFrobeniusPolynomial_monic W hW f hf) hdeg'
  exact Module.FaithfullyFlat.of_linearEquiv Rv Dv
    (powerRootPrismMonicVarpiResidueAlgEquiv W hW f hf).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicVarpiFlat

/-! ## ϖ 係数の逆 Frobenius 入力を元の mod p 入力へ戻す

## 概要

R/ϖ から R/p への係数 Frobenius 同型は、逆 Frobenius 係数の入力の pd 表示を
元の多項式の mod p 入力の pd 表示へ送る。BS 著者版 Remark 7.15（著者版 p.62）の係数の追跡。

## 方針

無限根変数を固定する係数同型を主分冪表示へ持ち上げる。

## 規約

順方向の底環は R/ϖ → R/p。両環を暗黙に同一視せず、元の f の mod p 像を明示する。

## 使われ方

元の実完備化剰余の通常テンソル底変換を、元の入力の pd 表示へ結び付ける。
-/

@[expose] public noncomputable section PowerRootVarpiPrimeFrobeniusPD

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p hp
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Rp" => (A ⧸ W.ideal) ⧸ Ideal.span {(p : A ⧸ W.ideal)}
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "Np" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rp p hp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "bv" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ W.ideal)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW

/-- 概要：係数 Frobenius は逆 Frobenius 係数を元の mod p 係数へ戻す。
方針：既存の二重商の代表元公式と Frobenius の逆合成を使う。
規約：任意の元 a∈A を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の入力多項式の照合。 -/
theorem varpiPrimeFrobenius_inverse_coeff (a : A) : evp (bv ((frob).symm a)) = bp a := by
  simp only [RingHom.comp_apply]
  rw [perfectPrismVarpiFrobeniusQuotientEquiv_mk]
  change bp ((frob) ((frob).symm a)) = bp a
  rw [RingEquiv.apply_symm_apply]

/-- 概要：係数 Frobenius は同じ指数の無限根多項式環の環同型を与える。
方針：加法モノイド環の係数同型を使う。
規約：無限根変数の番号は固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 入力を保つ係数比較。 -/
def powerRootVarpiPrimeFrobeniusEquiv : Nv ≃+* Np := AddMonoidAlgebra.mapRingEquiv G evp

/-- 概要：無限根同型は係数に指定 Frobenius 同型を作用させる。
方針：零指数の単項式の公式を使う。
規約：R/ϖ の全ての係数を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の半線形性。 -/
theorem powerRootVarpiPrimeFrobeniusEquiv_coeff (a : Rv) :
    powerRootVarpiPrimeFrobeniusEquiv W hW (algebraMap Rv Nv a) = algebraMap Rp Np (evp a) := by
  simp only [powerRootVarpiPrimeFrobeniusEquiv, AddMonoidAlgebra.coe_algebraMap,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AddMonoidAlgebra.mapRingEquiv_single]

/-- 概要：係数 Frobenius 同型は全ての根変数を固定する。
方針：係数 1 の単項式の公式を使う。
規約：全段 n を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の多項式評価の自然性。 -/
theorem powerRootVarpiPrimeFrobeniusEquiv_variable (n : ℕ) :
    powerRootVarpiPrimeFrobeniusEquiv W hW (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rv p hp n) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n := by
  simp only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable, powerRootVarpiPrimeFrobeniusEquiv,
    AddMonoidAlgebra.mapRingEquiv_single, map_one]

variable (f : Polynomial A)
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp
  (Polynomial.map bv (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "zp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "Dp" => PrincipalDPPresentation Np zp

/-- 概要：逆 Frobenius 係数の入力は元の f の mod p 評価に送られる。
方針：評価と係数環射の可換性に逆係数の相殺公式を適用する。
規約：モニック性・次数・p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正確な pd 入力の照合。 -/
theorem powerRootVarpiPrimeFrobeniusEquiv_input :
    powerRootVarpiPrimeFrobeniusEquiv W hW zv = zp := by
  let q : Nv →+* Np := (powerRootVarpiPrimeFrobeniusEquiv W hW).toRingHom
  change q zv = zp
  unfold _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    show q (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rv p hp 0) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp 0 from
        powerRootVarpiPrimeFrobeniusEquiv_variable W hW 0,
    Polynomial.eval₂_map, perfectPrismInverseFrobeniusPolynomial, Polynomial.eval₂_map,
    Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro a
  change powerRootVarpiPrimeFrobeniusEquiv W hW (algebraMap Rv Nv (bv ((frob).symm a))) =
    algebraMap Rp Np (bp a)
  rw [powerRootVarpiPrimeFrobeniusEquiv_coeff, varpiPrimeFrobenius_inverse_coeff]

/-- 概要：係数 Frobenius は逆係数入力の pd 表示を元の mod p 入力の表示へ送る。
方針：入力を保つ無限根環同型を主分冪表示へ持ち上げる。
規約：底環は明示した R/ϖ と R/p。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実テンソル引戻しの比較先。 -/
def powerRootVarpiPrimeFrobeniusPDEquiv : Dv ≃+* Dp :=
  principalDPRingEquivOfEq (powerRootVarpiPrimeFrobeniusEquiv W hW) zv zp
    (powerRootVarpiPrimeFrobeniusEquiv_input W hW f)

/-- 概要：pd 表示の同型は R/ϖ 係数に指定 Frobenius を作用させる。
方針：入力環の係数公式と係数作用の塔を合成する。
規約：全ての剰余係数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実底変換同型の半線形性。 -/
theorem powerRootVarpiPrimeFrobeniusPDEquiv_coeff (a : Rv) :
    powerRootVarpiPrimeFrobeniusPDEquiv W hW f (algebraMap Rv Dv a) =
      algebraMap Rp Dp (evp a) := by
  rw [IsScalarTower.algebraMap_apply Rv Nv Dv, powerRootVarpiPrimeFrobeniusPDEquiv,
    principalDPRingEquivOfEq_coeff, powerRootVarpiPrimeFrobeniusEquiv_coeff]
  exact (IsScalarTower.algebraMap_apply Rp Np Dp (evp a)).symm

/-- 概要：pd 表示の全標準生成元は同じ次数の標準生成元に送られる。
方針：主分冪同型の生成元公式。
規約：零次数を含む全次数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実分冪構造の比較。 -/
theorem powerRootVarpiPrimeFrobeniusPDEquiv_generator (n : ℕ) :
    powerRootVarpiPrimeFrobeniusPDEquiv W hW f (principalDPGenerator zv n) =
      principalDPGenerator zp n := principalDPRingEquivOfEq_generator _ _ _ _ n

end SerrePositivity.BhattScholze.Andre

end PowerRootVarpiPrimeFrobeniusPD

/-! ## André mod p 入力の分冪構造の移行用 import

## 概要

元の mod p 入力に関する係数比較の import を保持する。BS 著者版 Remark 7.15(1)（著者版 p.62）。

## 方針

旧 hpR 付き3宣言を削除し、`Unconditional/MonicPDEnvelope.lean` の同名の
`_of_unconditional` 版を集約から公開する。原典とは異なる射影的係数商と構造移送の経路。

## 規約

モニック入力・同じ mod p 入力・同じ指定イデアルを保持し、正次数を追加しない。

## 使われ方

既存の import 経路と係数比較を維持し、実 Frobenius 引戻しに無条件の分冪構造を適用する。
-/

/-! ## 無限根モニック入力の mod(p,d) 正則性

## 概要

モニック入力は任意の係数イデアル商後も正則。
prism 商が p 正則なら、無限根入力の mod p で d とモニック入力は正則対となる。
BS 著者版 Remark 7.15（著者版 p.62）の p ねじれなしの場合の有限関係商への入力。

## 方針

係数イデアル商との交換とモニック入力の正則性を使い、
p,d の正則性を平坦な無限根環へ移す。

## 規約

prism 商の p 正則性は明示仮定。一般の根付き存在定理へ追加しない。

## 使われ方

有限 raw δ 関係商の p 正則性と mod p の d 正則性の同時帰納法の初期値。
-/

@[expose] public noncomputable section PowerRootMonicModPairRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) (hp : 0 < p)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp

/-- 概要：任意の係数イデアル商後も無限根モニック入力は正則。
方針：係数商同型で商係数上のモニック入力の正則性へ移す。
規約：係数イデアル I の正則性や主性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の mod(p,d) 正則入力。 -/
theorem powerRootPolynomial_monic_mod_ideal_regular (I : Ideal A)
    (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular (P ⧸ I.map (algebraMap A P))
      (Ideal.Quotient.mk (I.map (algebraMap A P)) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap A p hp f)) := by
  let e := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootCoefficientIdealQuotientEquiv A p hp I
  have he : e (Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap A p hp f)) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap (A ⧸ I) p hp (f.map (Ideal.Quotient.mk I)) := by
    rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootCoefficientIdealQuotientEquiv_mk, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootCoefficientIdealQuotientMap_baseMap]
  have hr := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomial_monic_regular (A ⧸ I) p hp
    (f.map (Ideal.Quotient.mk I)) (hf.map _)
  intro x z hxz
  apply e.injective
  apply hr
  simpa only [smul_eq_mul, map_mul, he] using congrArg e hxz

/-- 概要：無限根入力の実二元係数商でモニック入力は正則。
方針：(p,d) の像を二元生成イデアルと同定する。
規約：d は任意の係数元。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限源の初期正則対。 -/
theorem powerRootPolynomial_monic_mod_pair_regular (d : A)
    (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular (P ⧸ Ideal.span {(p : P), algebraMap A P d})
      (Ideal.Quotient.mk (Ideal.span {(p : P), algebraMap A P d})
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap A p hp f)) := by
  have he : (Ideal.span {(p : A), d}).map (algebraMap A P) =
      Ideal.span {(p : P), algebraMap A P d} := by
    rw [Ideal.map_span, Set.image_pair, map_natCast]
  rw [← he]
  exact powerRootPolynomial_monic_mod_ideal_regular p hp _ f hf

variable [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "Pp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p (Nat.Prime.pos (Fact.out : p.Prime))
local notation "dP" => algebraMap A Pp W.generator

include hW in
/-- 概要：p 正則な prism 商では無限根入力の d の mod p 像も正則。
方針：係数上の d の mod p 正則性を無限根環の自由性で移す。
規約：prism 商 R の p 正則性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限 δ 関係商の初期値。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の初期線形除算関係の正則対。 -/
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
  have he := principalDoubleQuotEquiv_mk (p : Pp) dP (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap A p
    (Nat.Prime.pos (Fact.out : p.Prime)) f)
  change e (Ideal.Quotient.mk _ (Ideal.Quotient.mk _
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap A p (Nat.Prime.pos (Fact.out : p.Prime)) f))) = _ at he
  simpa only [smul_eq_mul, map_mul, he] using congrArg e hxz

include hW in
/-- 概要：最初の mod p 線形除算関係は無限根モニック入力でも正則。
方針：d の mod p 正則性を最高係数の正則性判定へ渡す。
規約：変数族 τ は任意で、prism 商の p 正則性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最初の有限関係商の p 正則性への入力。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限関係商の同時帰納法の初期値。 -/
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

end PowerRootMonicModPairRegular

/-! ## André 無限根モニック raw 包の有限段の条件付き正則対

## 概要

p 正則な prism 商を持つ完全 prism 上で、全有限段の p と mod p の生成元は正則。
BS 著者版 Remark 7.15（著者版 p.62）の p ねじれなしの場合の源の計算。

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

@[expose] public noncomputable section PowerRootPrismMonicRawRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
/-- 概要：無限根入力の同じ宇宙の一元自由 δ 環の台環を固定する。
方針：一元添字型を宇宙付きで定義する。
規約：入力族と自由環で同じ添字型を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的 ghost 単射性の入力。 -/
abbrev PowerRootUnaryFreeDeltaRing (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p) :=
  RelativeFreeDeltaRing (R := _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp) PUnit.{u + 1}

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "I" => deltaDivisionFiniteRelationIdeal E dP a
local notation "Raw" => DeltaAdjoinDivision E dP a

include hpR hf in
/-- 概要：無限根モニック入力の全有限段で p と mod p の生成元は正則。
方針：モニック正則性・prism の正則対・ghost 単射性を内部で供給して帰納する。
規約：正次数は不要で、prism 商の p 正則性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 包の p 正則性の具体的入力。 -/
theorem powerRootPrismMonicFinite_all_regular (N : ℕ) :
    let B := L₀ ⧸ I N
    IsSMulRegular B (p : B) ∧ IsSMulRegular (B ⧸ Ideal.span {(p : B)})
      (Ideal.Quotient.mk (Ideal.span {(p : B)}) (Ideal.Quotient.mk (I N) (MvPolynomial.C dP))) := by
  have hpP := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomial_primeRegular p hW.p_mul_injective
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

end PowerRootPrismMonicRawRegular

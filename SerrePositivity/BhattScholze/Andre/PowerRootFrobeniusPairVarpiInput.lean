module

public import SerrePositivity.BhattScholze.Andre.PowerRootCoefficientIdealQuotient
public import SerrePositivity.BhattScholze.Andre.PerfectPrismFrobeniusPairToVarpi
public import SerrePositivity.BhattScholze.Andre.PowerRootMonicModPrimePDEnvelope

/-!
# André E1・E2：Frobenius 二元商の無限根入力と ϖ 係数

## 概要

無限根環 P の (p,d) 商は R/ϖ 上の無限根環と環同型。
係数は逆 Frobenius で移り、根変数の番号は保つ。
BS Rem 7.15（著者版 p.62）の入力比較で係数変更を明示する。

## 方針

係数イデアル商との交換と、二元商から ϖ 商への逆係数同型を合成する。

## 規約

入力は係数を逆 Frobenius で移した多項式となる。元の f との同一視は主張しない。

## 使われ方

実完備化の剰余を R/ϖ 上の具体的な主分冪表示に接続する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "dP" => algebraMap A P W.generator
local notation "K" => Ideal.span {(p : A), W.generator}
local notation "KP" => Ideal.span {(p : P), dP}
local notation "e" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)

/-- 概要：無限根入力の二元商と R/ϖ 上の同じ無限根環の同型。
方針：任意係数イデアル商との交換と逆係数 Frobenius を合成する。
規約：指数モノイドは変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の主分冪入力の係数移送。 -/
def powerRootFrobeniusPairVarpiInputEquiv : (P ⧸ KP) ≃+* Nv :=
  ((Ideal.quotEquivOfEq (show KP = (K).map (algebraMap A P) by
    rw [Ideal.map_span, Set.image_pair, map_natCast])).trans
      (powerRootCoefficientIdealQuotientEquiv A p hp K)).trans
    (AddMonoidAlgebra.mapRingEquiv G (perfectPrismVarpiToFrobeniusPairEquiv W hW).symm)

/-- 概要：入力同型は単項式の係数に逆 Frobenius を適用する。
方針：商比較とモノイド環の係数写像の公式を合成する。
規約：指数を変えない。
使われ方：BS Rem 7.15（著者版 p.62）の具体的係数作用の確認。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_single (q : G) (r : A) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (AddMonoidAlgebra.single q r)) =
        AddMonoidAlgebra.single q (barr ((e).symm r)) := by
  simp only [powerRootFrobeniusPairVarpiInputEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, powerRootCoefficientIdealQuotientEquiv_mk,
    powerRootCoefficientIdealQuotientMap_single, AddMonoidAlgebra.mapRingEquiv_single,
    perfectPrismVarpiToFrobeniusPairEquiv_symm_mk]

/-- 概要：入力同型の標準係数上の公式。
方針：零指数の単項式を計算する。
規約：元の全ての係数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の pd 係数作用の移送。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_coeff (r : A) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (algebraMap A P r)) = algebraMap Rv Nv (barr ((e).symm r)) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootFrobeniusPairVarpiInputEquiv_single W hW 0 r

/-- 概要：入力同型は全ての根変数の番号を保つ。
方針：係数 1 の単項式の比較を使う。
規約：全ての段 n を含める。
使われ方：BS Rem 7.15（著者版 p.62）の一元多項式評価の比較。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_variable (n : ℕ) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (powerRootPolynomialVariable A p hp n)) =
        powerRootPolynomialVariable Rv p hp n := by
  simpa only [powerRootPolynomialVariable, map_one] using
    powerRootFrobeniusPairVarpiInputEquiv_single W hW _ 1

/-- 概要：元の無限根環から ϖ 係数の無限根環への通常比較射。
方針：二元商射と入力同型を合成する。
規約：逆 Frobenius 係数作用を持つ。
使われ方：BS Rem 7.15（著者版 p.62）の評価の自然性を適用するための環射。 -/
def powerRootFrobeniusPairVarpiInputMap : P →+* Nv :=
  (powerRootFrobeniusPairVarpiInputEquiv W hW).toRingHom.comp (Ideal.Quotient.mk KP)

/-- 概要：通常入力多項式は逆 Frobenius で係数変更した評価へ送られる。
方針：評価の自然性と標準係数・根変数の公式を使う。
規約：モニック性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の主分冪表示の正確な入力。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_baseMap (f : Polynomial A) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (powerRootPolynomialBaseMap A p hp f)) =
        powerRootPolynomialBaseMap Rv p hp
          ((perfectPrismInverseFrobeniusPolynomial W hW f).map barr) := by
  let F := powerRootFrobeniusPairVarpiInputMap W hW
  change F (powerRootPolynomialBaseMap A p hp f) = _
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    show F (powerRootPolynomialVariable A p hp 0) = powerRootPolynomialVariable Rv p hp 0 from
      powerRootFrobeniusPairVarpiInputEquiv_variable W hW 0,
    perfectPrismInverseFrobeniusPolynomial, Polynomial.eval₂_map, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro r
  exact powerRootFrobeniusPairVarpiInputEquiv_coeff W hW r

/-- 概要：名前付きモニック入力も同じ逆 Frobenius 係数評価へ送られる。
方針：入力の定義を一度展開して評価公式を使う。
規約：元の多項式を暗黙に変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の標準主 pd 同型への入力等式。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_input (f : Polynomial A) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (powerRootMonicPDInput p f)) =
        powerRootPolynomialBaseMap Rv p hp
          ((perfectPrismInverseFrobeniusPolynomial W hW f).map barr) := by
  unfold powerRootMonicPDInput
  exact powerRootFrobeniusPairVarpiInputEquiv_baseMap W hW f

end SerrePositivity.BhattScholze.Andre

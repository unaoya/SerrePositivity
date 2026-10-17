module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiFrobeniusQuotient

/-!
# André E1・E2：二元係数商から ϖ 商への逆 Frobenius

## 概要

完全 prism の係数二元商 A/(p,d) を R/ϖ と具体的に比較する。
BS Rem 7.15（著者版 p.62）の係数作用を追う。

## 方針

既存の二重商と係数 Frobenius の二元イデアル比較を合成する。
逆方向が各係数に逆 Frobenius を適用することを計算する。

## 規約

prism 商の p 正則性や非零性を仮定しない。

## 使われ方

主 pd 表示の入力多項式がどの係数写像で移るかを明示する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "e" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "x" => perfectPrismVarpiLift W hW
local notation "K" => Ideal.span {(p : A), W.generator}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)

/-- 概要：ϖ 商から一重二元係数商への具体的 Frobenius 同型。
方針：二重商を一重商にし、Frobenius で (d,x) を (p,d) へ送る。
規約：元の係数作用を代表元で追える向きを選ぶ。
使われ方：BS Rem 7.15（著者版 p.62）の逆係数写像の構成。 -/
def perfectPrismVarpiToFrobeniusPairEquiv : Rv ≃+* A ⧸ K :=
  (principalDoubleQuotEquiv W.generator x).trans
    (Ideal.quotientEquiv _ _ e (perfectPrismVarpiFrobenius_pairIdeal W hW).symm)

/-- 概要：二元係数商への同型は代表元に Frobenius を適用する。
方針：二重商と標準商同型の代表元公式を使う。
規約：全ての r∈A を含む。
使われ方：BS Rem 7.15（著者版 p.62）の多項式係数の移送。 -/
theorem perfectPrismVarpiToFrobeniusPairEquiv_mk (r : A) :
    perfectPrismVarpiToFrobeniusPairEquiv W hW (barr r) = Ideal.Quotient.mk K (e r) := by
  rw [perfectPrismVarpiToFrobeniusPairEquiv, RingEquiv.trans_apply]
  change Ideal.quotientEquiv _ _ _ _
    (principalDoubleQuotEquiv W.generator x (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r))) = _
  rw [principalDoubleQuotEquiv_mk, Ideal.quotientEquiv_mk]

/-- 概要：逆係数同型は Frobenius 像の剰余を元の ϖ 剰余へ戻す。
方針：順写像の代表元公式と逆合成を使う。
規約：Frobenius は完全 δ 環の指定自己同型。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数作用の照合。 -/
theorem perfectPrismVarpiToFrobeniusPairEquiv_symm_frobenius (r : A) :
    (perfectPrismVarpiToFrobeniusPairEquiv W hW).symm (Ideal.Quotient.mk K (e r)) = barr r := by
  rw [← perfectPrismVarpiToFrobeniusPairEquiv_mk, RingEquiv.symm_apply_apply]

/-- 概要：逆係数同型は任意の代表元に逆 Frobenius を適用する。
方針：Frobenius の全射性と前公式を使う。
規約：係数を暗黙に同一視せず値を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の入力多項式の正確な比較。 -/
theorem perfectPrismVarpiToFrobeniusPairEquiv_symm_mk (r : A) :
    (perfectPrismVarpiToFrobeniusPairEquiv W hW).symm (Ideal.Quotient.mk K r) =
      barr ((e).symm r) := by
  have h := perfectPrismVarpiToFrobeniusPairEquiv_symm_frobenius W hW ((e).symm r)
  simpa only [RingEquiv.apply_symm_apply] using h

/-- 概要：逆 Frobenius による入力多項式の係数変更。
方針：全係数を完全 δ 環の逆 Frobenius で写す。
規約：この多項式を元の f と同一視しない。
使われ方：BS Rem 7.15（著者版 p.62）の主 pd 表示を ϖ 係数へ移す入力。 -/
def perfectPrismInverseFrobeniusPolynomial (f : Polynomial A) : Polynomial A :=
  f.map (e).symm.toRingHom

/-- 概要：逆 Frobenius で係数変更したモニック多項式もモニック。
方針：モニック性の環射による保存を使う。
規約：正次数は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の移送後の正則性と自由性。 -/
theorem perfectPrismInverseFrobeniusPolynomial_monic (f : Polynomial A) (hf : f.Monic) :
    (perfectPrismInverseFrobeniusPolynomial W hW f).Monic := hf.map _

end SerrePositivity.BhattScholze.Andre

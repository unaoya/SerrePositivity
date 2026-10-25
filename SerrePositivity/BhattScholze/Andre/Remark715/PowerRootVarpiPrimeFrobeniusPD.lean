module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicVarpiFlat
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismVarpiFrobeniusQuotient

/-!
# André E1・E2：ϖ 係数の逆 Frobenius 入力を元の mod p 入力へ戻す

## 概要

R/ϖ から R/p への係数 Frobenius 同型は、逆 Frobenius 係数の入力の pd 表示を
元の多項式の mod p 入力の pd 表示へ送る。BS Rem 7.15（著者版 p.62）の係数の追跡。

## 方針

無限根変数を固定する係数同型を主分冪表示へ持ち上げる。

## 規約

順方向の底環は R/ϖ → R/p。両環を暗黙に同一視せず、元の f の mod p 像を明示する。

## 使われ方

元の実完備化剰余の通常テンソル底変換を、元の入力の pd 表示へ結び付ける。
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
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Rp" => (A ⧸ W.ideal) ⧸ Ideal.span {(p : A ⧸ W.ideal)}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "Np" => PowerRootPolynomial Rp p hp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "bv" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ W.ideal)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW

/-- 概要：係数 Frobenius は逆 Frobenius 係数を元の mod p 係数へ戻す。
方針：既存の二重商の代表元公式と Frobenius の逆合成を使う。
規約：任意の元 a∈A を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の元の入力多項式の照合。 -/
theorem varpiPrimeFrobenius_inverse_coeff (a : A) : evp (bv ((frob).symm a)) = bp a := by
  simp only [RingHom.comp_apply]
  rw [perfectPrismVarpiFrobeniusQuotientEquiv_mk]
  change bp ((frob) ((frob).symm a)) = bp a
  rw [RingEquiv.apply_symm_apply]

/-- 概要：係数 Frobenius は同じ指数の無限根多項式環の環同型を与える。
方針：加法モノイド環の係数同型を使う。
規約：無限根変数の番号は固定する。
使われ方：BS Rem 7.15（著者版 p.62）の pd 入力を保つ係数比較。 -/
def powerRootVarpiPrimeFrobeniusEquiv : Nv ≃+* Np := AddMonoidAlgebra.mapRingEquiv G evp

/-- 概要：無限根同型は係数に指定 Frobenius 同型を作用させる。
方針：零指数の単項式の公式を使う。
規約：R/ϖ の全ての係数を含む。
使われ方：BS Rem 7.15（著者版 p.62）の半線形性。 -/
theorem powerRootVarpiPrimeFrobeniusEquiv_coeff (a : Rv) :
    powerRootVarpiPrimeFrobeniusEquiv W hW (algebraMap Rv Nv a) = algebraMap Rp Np (evp a) := by
  simp only [powerRootVarpiPrimeFrobeniusEquiv, AddMonoidAlgebra.coe_algebraMap,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AddMonoidAlgebra.mapRingEquiv_single]

/-- 概要：係数 Frobenius 同型は全ての根変数を固定する。
方針：係数 1 の単項式の公式を使う。
規約：全段 n を含む。
使われ方：BS Rem 7.15（著者版 p.62）の多項式評価の自然性。 -/
theorem powerRootVarpiPrimeFrobeniusEquiv_variable (n : ℕ) :
    powerRootVarpiPrimeFrobeniusEquiv W hW (powerRootPolynomialVariable Rv p hp n) =
      powerRootPolynomialVariable Rp p hp n := by
  simp only [powerRootPolynomialVariable, powerRootVarpiPrimeFrobeniusEquiv,
    AddMonoidAlgebra.mapRingEquiv_single, map_one]

variable (f : Polynomial A)
local notation "zv" => powerRootPolynomialBaseMap Rv p hp
  (Polynomial.map bv (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "zp" => powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "Dp" => PrincipalDPPresentation Np zp

/-- 概要：逆 Frobenius 係数の入力は元の f の mod p 評価に送られる。
方針：評価と係数環射の可換性に逆係数の相殺公式を適用する。
規約：モニック性・次数・p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の正確な pd 入力の照合。 -/
theorem powerRootVarpiPrimeFrobeniusEquiv_input :
    powerRootVarpiPrimeFrobeniusEquiv W hW zv = zp := by
  let q : Nv →+* Np := (powerRootVarpiPrimeFrobeniusEquiv W hW).toRingHom
  change q zv = zp
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    show q (powerRootPolynomialVariable Rv p hp 0) =
      powerRootPolynomialVariable Rp p hp 0 from
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
使われ方：BS Rem 7.15（著者版 p.62）の実テンソル引戻しの比較先。 -/
def powerRootVarpiPrimeFrobeniusPDEquiv : Dv ≃+* Dp :=
  principalDPRingEquivOfEq (powerRootVarpiPrimeFrobeniusEquiv W hW) zv zp
    (powerRootVarpiPrimeFrobeniusEquiv_input W hW f)

/-- 概要：pd 表示の同型は R/ϖ 係数に指定 Frobenius を作用させる。
方針：入力環の係数公式と係数作用の塔を合成する。
規約：全ての剰余係数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の実底変換同型の半線形性。 -/
theorem powerRootVarpiPrimeFrobeniusPDEquiv_coeff (a : Rv) :
    powerRootVarpiPrimeFrobeniusPDEquiv W hW f (algebraMap Rv Dv a) =
      algebraMap Rp Dp (evp a) := by
  rw [IsScalarTower.algebraMap_apply Rv Nv Dv, powerRootVarpiPrimeFrobeniusPDEquiv,
    principalDPRingEquivOfEq_coeff, powerRootVarpiPrimeFrobeniusEquiv_coeff]
  exact (IsScalarTower.algebraMap_apply Rp Np Dp (evp a)).symm

/-- 概要：pd 表示の全標準生成元は同じ次数の標準生成元に送られる。
方針：主分冪同型の生成元公式。
規約：零次数を含む全次数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の実分冪構造の比較。 -/
theorem powerRootVarpiPrimeFrobeniusPDEquiv_generator (n : ℕ) :
    powerRootVarpiPrimeFrobeniusPDEquiv W hW f (principalDPGenerator zv n) =
      principalDPGenerator zp n := principalDPRingEquivOfEq_generator _ _ _ _ n

end SerrePositivity.BhattScholze.Andre

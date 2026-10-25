module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionCoefficientAut
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismVarpi

/-!
# André E1・E2：raw Frobenius 係数変更と二つの剰余

## 概要

完全 δ 環の distinguished 元 d に対し、raw 包の (d,φ⁻¹(d)) 商は
Frobenius で移した raw 包の (p,d) 商と環同型。
BS Rem 7.15（著者版 p.62）の二重剰余の代数的比較。

## 方針

係数自己同型による raw 同型を二元イデアルの商へ降ろす。
φ(d)=d^p+pδ(d) と δ(d) の単元性で像イデアルを (p,d) と同定する。

## 規約

未完備の raw 包を扱う。これだけで原典の完備化済みの比較を主張しない。

## 使われ方

Hodge–Tate 商と ϖ 商に対応する二元イデアルを Frobenius の両側で追跡する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (e : A ≃+* A) (he : D.IsDeltaHom D e.toRingHom)
variable (d : A) (a : σ → A)
local notation "L" => DeltaAdjoinDivision D d a
local notation "M" => DeltaAdjoinDivision D (e d) (fun s => e (a s))
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "jM" => deltaAdjoinDivisionMap D (e d) (fun s => e (a s))
local notation "F" => deltaDivisionCoefficientAutEquiv D e he d a

/-- 概要：raw 係数自己同型は任意の二元係数イデアルを対応する像へ送る。
方針：span の像を二つの係数元で計算する。
規約：二元は除算分母と一致する必要はない。
使われ方：BS Rem 7.15（著者版 p.62）の二重剰余への降下。 -/
theorem deltaDivisionCoefficientAut_pairIdeal (r s : A) :
    (Ideal.span {jL r, jL s}).map (F).toRingHom = Ideal.span {jM (e r), jM (e s)} := by
  rw [Ideal.map_span, Set.image_pair]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    deltaDivisionCoefficientAutEquiv_coeff]

/-- 概要：raw 係数自己同型は二元係数イデアルの実商の同型を誘導する。
方針：像イデアルの計算を標準商同型へ供給する。
規約：両側とも実際の span の商を使う。
使われ方：BS Rem 7.15（著者版 p.62）の剰余台環の比較。 -/
def deltaDivisionCoefficientAutResidueEquiv (r s : A) :
    (L ⧸ Ideal.span {jL r, jL s}) ≃+* (M ⧸ Ideal.span {jM (e r), jM (e s)}) :=
  Ideal.quotientEquiv _ _ F (deltaDivisionCoefficientAut_pairIdeal D e he d a r s).symm

/-- 概要：raw 剰余比較は代表元を元の raw 同型で送る。
方針：商同型の標準代表元公式を使う。
規約：raw 包の任意の元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数・除算変数の照合。 -/
theorem deltaDivisionCoefficientAutResidueEquiv_mk (r s : A) (t : L) :
    deltaDivisionCoefficientAutResidueEquiv D e he d a r s (Ideal.Quotient.mk _ t) =
      Ideal.Quotient.mk _ (F t) := rfl

variable (hD : D.IsPerfect)
local notation "φ" => D.frobeniusLift
local notation "x" => RingEquiv.symm (DeltaStructure.frobeniusEquiv D hD) d
local notation "Mφ" => DeltaAdjoinDivision D (φ d) (fun s => φ (a s))
local notation "jφ" => deltaAdjoinDivisionMap D (φ d) (fun s => φ (a s))

/-- 概要：Frobenius で移した二元イデアルは (p,d) の係数像。
方針：φ(φ⁻¹(d))=d と distinguished 元の二元イデアル計算を使う。
規約：等式は Frobenius 側の raw 包内で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の二重剰余の標準化。 -/
theorem deltaDivisionFrobenius_pairIdeal (hd : D.IsDistinguished d) :
    Ideal.span {jφ (φ d), jφ (φ x)} = Ideal.span {(p : Mφ), jφ d} := by
  have hx : φ x = d := (D.frobeniusEquiv hD).apply_symm_apply d
  rw [hx]
  have h := congrArg (Ideal.map jφ) (distinguished_frobenius_pair_span D d hd)
  simpa only [Ideal.map_span, Set.image_pair, map_natCast] using h

/-- 概要：raw 包の (d,φ⁻¹(d)) 商は Frobenius 側の (p,d) 商と環同型。
方針：Frobenius の raw 同型を商へ降ろし、像の二元イデアルを標準化する。
規約：d は distinguished、係数 δ 環は完全とする。
使われ方：BS Rem 7.15（著者版 p.62）の完備化前の二重剰余比較。 -/
def deltaDivisionFrobeniusResidueEquiv (hd : D.IsDistinguished d) :
    (L ⧸ Ideal.span {jL d, jL x}) ≃+* (Mφ ⧸ Ideal.span {(p : Mφ), jφ d}) :=
  (deltaDivisionCoefficientAutResidueEquiv D (D.frobeniusEquiv hD)
    (D.frobeniusEquiv_isDeltaHom hD) d a d x).trans
      (Ideal.quotEquivOfEq (deltaDivisionFrobenius_pairIdeal D d a hD hd))

/-- 概要：二重剰余比較は元の係数 b を Frobenius 係数 φ(b) へ送る。
方針：raw 係数公式と二つの商同型の代表元公式を使う。
規約：同型は元の A 係数に関して Frobenius 半線形。
使われ方：BS Rem 7.15（著者版 p.62）の残余係数作用の追跡。 -/
theorem deltaDivisionFrobeniusResidueEquiv_coeff (hd : D.IsDistinguished d) (b : A) :
    deltaDivisionFrobeniusResidueEquiv D d a hD hd (Ideal.Quotient.mk _ (jL b)) =
      Ideal.Quotient.mk _ (jφ (φ b)) := by
  simp only [deltaDivisionFrobeniusResidueEquiv, RingEquiv.trans_apply,
    deltaDivisionCoefficientAutResidueEquiv_mk, deltaDivisionCoefficientAutEquiv_coeff]
  rfl

/-- 概要：二重剰余比較は初期除算変数の添字を保つ。
方針：raw 変数公式と商代表元公式を合成する。
規約：任意の入力族を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の根関係の残余座標の追跡。 -/
theorem deltaDivisionFrobeniusResidueEquiv_variable (hd : D.IsDistinguished d) (s : σ) :
    deltaDivisionFrobeniusResidueEquiv D d a hD hd
      (Ideal.Quotient.mk _ (deltaAdjoinDivisionVariable D d a s)) =
        Ideal.Quotient.mk _ (deltaAdjoinDivisionVariable D (φ d) (fun t => φ (a t)) s) := by
  simp only [deltaDivisionFrobeniusResidueEquiv, RingEquiv.trans_apply,
    deltaDivisionCoefficientAutResidueEquiv_mk, deltaDivisionCoefficientAutEquiv_variable]
  rfl

/-- 概要：raw 包の Hodge–Tate 型商の ϖ 型商を、Frobenius 側の同じ順序の p 商へ移す。
方針：二重主イデアル商を二元商にし、Frobenius 比較後に順序を戻す。
規約：ここでの商は未完備 raw 包の通常商。
使われ方：BS Rem 7.15（著者版 p.62）の T/ϖ に対応する代数的剰余。 -/
def deltaDivisionFrobeniusDoubleResidueEquiv (hd : D.IsDistinguished d) :
    ((L ⧸ Ideal.span {jL d}) ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span {jL d}) (jL x)}) ≃+*
        ((Mφ ⧸ Ideal.span {jφ d}) ⧸
          Ideal.span {(p : Mφ ⧸ Ideal.span {jφ d})}) :=
  ((((principalDoubleQuotEquiv (jL d) (jL x)).trans
    (deltaDivisionFrobeniusResidueEquiv D d a hD hd)).trans
      (Ideal.quotEquivOfEq Ideal.span_pair_comm)).trans
        (principalDoubleQuotEquiv (jφ d) (p : Mφ)).symm).trans
    (Ideal.quotEquivOfEq (show Ideal.span {Ideal.Quotient.mk (Ideal.span {jφ d}) (p : Mφ)} =
      Ideal.span {(p : Mφ ⧸ Ideal.span {jφ d})} by rw [map_natCast]))

/-- 概要：raw 二重商の比較は係数代表元 b を φ(b) へ送る。
方針：二元商への変換と Frobenius 剰余比較の係数公式を使う。
規約：二つの商の順序を保って公式を述べる。
使われ方：BS Rem 7.15（著者版 p.62）の T/ϖ の係数作用の追跡。 -/
theorem deltaDivisionFrobeniusDoubleResidueEquiv_coeff
    (hd : D.IsDistinguished d) (b : A) :
    deltaDivisionFrobeniusDoubleResidueEquiv D d a hD hd
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (jL b))) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (jφ (φ b))) := by
  have ht := principalDoubleQuotEquiv_mk (jφ d) (p : Mφ) (jφ (φ b))
  have ht' := (principalDoubleQuotEquiv (jφ d) (p : Mφ)).symm_apply_apply
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (jφ (φ b))))
  rw [ht] at ht'
  simp only [deltaDivisionFrobeniusDoubleResidueEquiv, RingEquiv.trans_apply]
  rw [principalDoubleQuotEquiv_mk, deltaDivisionFrobeniusResidueEquiv_coeff,
    Ideal.quotEquivOfEq_mk, ht', Ideal.quotEquivOfEq_mk]


end SerrePositivity.BhattScholze.Andre

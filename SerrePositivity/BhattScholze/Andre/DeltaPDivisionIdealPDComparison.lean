module

public import SerrePositivity.BhattScholze.DeltaPDivisionRawPrincipal
public import SerrePositivity.BhattScholze.Andre.PrincipalDPIdealQuotient
public import SerrePositivity.BhattScholze.Andre.DeltaDivisionPairResidueWitt

/-!
# André E1・E2：raw p 除算包の係数商と主 pd 表示

## 概要

正則な一元入力について、raw φ(y)/p 包の任意の係数商は係数商上の主分冪表示と環同型。
BS Cor 2.39（著者版 p.25）と Rem 7.15（p.62）の具体的剰余比較。

## 方針

既存の raw 包と主分冪表示の係数を保つ同型を商へ降ろし、表示の係数商と交換する。

## 規約

p 局所性・源の p 正則性・y mod p の正則性を明示する。
任意の係数イデアルに正則性は要求しない。実分冪構造の構成は別工程。

## 使われ方

Frobenius 分母を正規化した二元剰余を具体的 pd 包の台環へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun r : A => (p : A) * r))
variable (D : DeltaStructure p A) (y : A)
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "a" => fun _ : σ => D.frobeniusLift y
local notation "Raw" => DeltaAdjoinDivision D (p : A) a
local notation "j" => deltaAdjoinDivisionMap D (p : A) a
local notation "PD" => PrincipalDPPresentation A y
local notation "E" => deltaPDivisionRawPrincipalEquiv hA hpA D y hgL v hv hy

/-- 概要：raw p 除算と主分冪表示の同型は任意の係数イデアルの像を保つ。
方針：元の A 上の全係数公式から環射の合成を照合する。
規約：係数イデアル K は任意。
使われ方：BS Rem 7.15（著者版 p.62）の二元商への同型の降下。 -/
theorem deltaPDivisionIdealPD_map (K : Ideal A) :
    (K.map j).map (E).toRingHom = K.map (algebraMap A PD) := by
  rw [Ideal.map_map]
  congr 1
  ext r
  exact deltaPDivisionRawPrincipalEquiv_coeff hA hpA D y hgL v hv hy r

/-- 概要：raw p 除算包の係数イデアル商は係数商上の主分冪表示と環同型。
方針：raw 同型を商へ降ろし、主分冪表示と係数商の交換を合成する。
規約：モニック性ではなく y mod p の正則性を入力とする。
使われ方：BS Cor 2.39（著者版 p.25）、Rem 7.15（p.62）の具体的 pd 台環比較。 -/
def deltaPDivisionIdealPDEquiv (K : Ideal A) :
    (Raw ⧸ K.map j) ≃+*
      PrincipalDPPresentation (A ⧸ K) (Ideal.Quotient.mk K y) :=
  (Ideal.quotientEquiv _ _ E (deltaPDivisionIdealPD_map hA hpA D y hgL v hv hy K).symm).trans
    (principalDPIdealQuotientEquiv K y)

/-- 概要：係数商を通る raw-pd 同型は元の全係数を保つ。
方針：商の代表元公式と両同型の係数公式を合成する。
規約：全ての r∈A を含む。
使われ方：BS Rem 7.15（著者版 p.62）の係数の Frobenius 作用の追跡。 -/
theorem deltaPDivisionIdealPDEquiv_coeff (K : Ideal A) (r : A) :
    deltaPDivisionIdealPDEquiv hA hpA D y hgL v hv hy K (Ideal.Quotient.mk _ (j r)) =
      algebraMap (A ⧸ K) _ (Ideal.Quotient.mk K r) := by
  rw [deltaPDivisionIdealPDEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
    deltaPDivisionRawPrincipalEquiv_coeff, principalDPIdealQuotientEquiv_coeff]

/-- 概要：raw-pd 係数商同型は具体的な階乗生成元を標準分冪へ送る。
方針：raw 同型と主分冪係数商の生成元公式を使う。
規約：全ての次数 n を含む。
使われ方：BS Rem 7.15（著者版 p.62）の実分冪構造を移送するための公式。 -/
theorem deltaPDivisionIdealPDEquiv_factorial (K : Ideal A) (n : ℕ) :
    deltaPDivisionIdealPDEquiv hA hpA D y hgL v hv hy K
      (Ideal.Quotient.mk _
        (deltaPDivisionRawFactorialQuotient D (fun _ : σ => y) hA (default : σ) n)) =
      principalDPGenerator (Ideal.Quotient.mk K y) n := by
  rw [deltaPDivisionIdealPDEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
    deltaPDivisionRawPrincipalEquiv_factorial, principalDPIdealQuotientEquiv_generator]

/-- 概要：raw p 除算の二元剰余は A/(p,d) 上の主分冪表示と環同型。
方針：二元生成イデアルを元の係数イデアルの像と同定し、一般比較を適用する。
規約：d の distinguished 性はこの比較には不要。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化剰余との接続。 -/
def deltaPDivisionPairPDEquiv (d : A) :
    DeltaDivisionPairResidue D (p : A) a d ≃+*
      PrincipalDPPresentation (A ⧸ Ideal.span {(p : A), d})
        (Ideal.Quotient.mk (Ideal.span {(p : A), d}) y) :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : Raw), j d} =
    (Ideal.span {(p : A), d}).map j by
      rw [Ideal.map_span, Set.image_pair, map_natCast])).trans
    (deltaPDivisionIdealPDEquiv hA hpA D y hgL v hv hy (Ideal.span {(p : A), d}))

/-- 概要：二元剰余の raw-pd 同型は元の全係数を保つ。
方針：像イデアルの書換えと一般係数商の係数公式を使う。
規約：元の自然な係数射について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化の係数作用の移送。 -/
theorem deltaPDivisionPairPDEquiv_coeff (d r : A) :
    deltaPDivisionPairPDEquiv hA hpA D y hgL v hv hy d
        (deltaDivisionPairResidueBase D (p : A) a d r) =
      algebraMap (A ⧸ Ideal.span {(p : A), d}) _
        (Ideal.Quotient.mk (Ideal.span {(p : A), d}) r) := by
  change deltaPDivisionPairPDEquiv hA hpA D y hgL v hv hy d
    (Ideal.Quotient.mk _ (j r)) = _
  rw [deltaPDivisionPairPDEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact deltaPDivisionIdealPDEquiv_coeff hA hpA D y hgL v hv hy _ r

end SerrePositivity.BhattScholze.Andre

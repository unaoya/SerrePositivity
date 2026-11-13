module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DeltaDivisionWitt
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Varpi
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Completion
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiPD
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalPair
public import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
public import SerrePositivity.BhattScholze.Andre.Envelope.JetKoszul
public import SerrePositivity.BhattScholze.Delta.Division.Basic

/-!
# raw δ 除算包の完備化後の剰余と正則性

## 概要
完備化後の Frobenius 比較と二重剰余、Frobenius 側の剰余を raw へ戻すこと、p 除算剰余への接続、二元剰余と主 pd 表示、Frobenius 係数変更、有限 mod p 関係商・有限 δ 関係商の正則性の伝播、一元 raw 包の正則対と p 正則性。
BS 著者版 Remark 7.15 の包に向けて、δ 除算包の完備化後の剰余と正則性を調べる。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPD`、`PowerRootEnvelope/CompletionPrism`、`PowerRootEnvelope/Unconditional/Residue`、`Variants/MonicRootedExtension`。
-/

universe u v w

/-! ## 実完備化後の Frobenius 比較と二重剰余

## 概要

完全 δ 環上の distinguished 元 d に対し、raw 包の実導来完備化を取った後の
(d,φ⁻¹(d)) 商は、Frobenius 側の実完備化後の (p,d) 商と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 比較の剰余への降下。

## 方針

実完備化同型の係数公式を使って二元イデアルの像を計算し、通常商同型へ降ろす。

## 規約

完備化と剰余の順序を交換する主張は含めない。実完備化 H⁰ を取った後の通常商を扱う。

## 使われ方

完備化済みの剰余と未完備 pd 包との後続比較に、係数作用を指定した同型を供給する。
-/

@[expose] public noncomputable section DeltaDivisionFrobeniusCompletedResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (a : σ → A)
local notation "φ" => D.frobeniusLift
local notation "e" => DeltaStructure.frobeniusEquiv D hD
local notation "x" => RingEquiv.symm (DeltaStructure.frobeniusEquiv D hD) d
local notation "L" => DeltaAdjoinDivision D d a
local notation "M" => DeltaAdjoinDivision D (e d) (fun s => e (a s))
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "jM" => deltaAdjoinDivisionMap D (e d) (fun s => e (a s))
local notation "HL" => PDCompletionH0 L p (jL d)
local notation "HM" => PDCompletionH0 M p (jM (e d))
local notation "uL" => pdCompletionUnit L p (jL d)
local notation "uM" => pdCompletionUnit M p (jM (e d))
local notation "F" => deltaDivisionCoefficientPDCompletionEquiv D
  (DeltaStructure.frobeniusEquiv D hD) (DeltaStructure.frobeniusEquiv_isDeltaHom D hD) d a

/-- 概要：実完備化同型は (d,φ⁻¹(d)) の係数像を (p,d) の係数像へ送る。
方針：標準完備化像の係数公式と distinguished 元の二元イデアル計算を使う。
規約：イデアルは実 H⁰ の環内で取る。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化後の剰余比較への入力。 -/
theorem deltaDivisionFrobeniusCompleted_pairIdeal (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (e d))
    (Ideal.span {uL (jL d), uL (jL x)}).map (F).toRingHom =
      Ideal.span {(p : HM), uM (jM d)} := by
  let := pdCompletionCommRing L p (jL d)
  let := pdCompletionCommRing M p (jM (e d))
  have hc (b : A) : F (uL (jL b)) = uM (jM (φ b)) :=
    deltaDivisionCoefficientPDCompletionEquiv_coeff D (D.frobeniusEquiv hD)
      (D.frobeniusEquiv_isDeltaHom hD) d a b
  have hx : φ x = d := (D.frobeniusEquiv hD).apply_symm_apply d
  rw [Ideal.map_span, Set.image_pair]
  change Ideal.span {F (uL (jL d)), F (uL (jL x))} = _
  rw [hc, hc, hx]
  have h := congrArg (Ideal.map ((uM).comp jM)) (distinguished_frobenius_pair_span D d hd)
  simpa only [Ideal.map_span, Set.image_pair, RingHom.comp_apply, map_natCast] using h

/-- 概要：実完備化後の (d,φ⁻¹(d)) 商は Frobenius 側の (p,d) 商と環同型。
方針：像イデアルの計算を実完備化同型からの標準商同型へ供給する。
規約：完備化と剰余を交換せず、完備化済みの両環で商を取る。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の Frobenius 剰余比較。 -/
def deltaDivisionFrobeniusCompletedResidueEquiv (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (e d))
    (HL ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+*
      (HM ⧸ Ideal.span {(p : HM), uM (jM d)}) := by
  let := pdCompletionCommRing L p (jL d)
  let := pdCompletionCommRing M p (jM (e d))
  exact Ideal.quotientEquiv _ _ F (deltaDivisionFrobeniusCompleted_pairIdeal D hD d a hd).symm

/-- 概要：実完備化の剰余同型は元の係数代表元 b を φ(b) へ送る。
方針：商同型の代表元公式と完備化比較の係数公式を使う。
規約：元の A 係数射と標準完備化単位を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包比較へ渡す係数作用。 -/
theorem deltaDivisionFrobeniusCompletedResidueEquiv_coeff
    (hd : D.IsDistinguished d) (b : A) :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (e d))
    deltaDivisionFrobeniusCompletedResidueEquiv D hD d a hd
      (Ideal.Quotient.mk _ (uL (jL b))) = Ideal.Quotient.mk _ (uM (jM (φ b))) := by
  let := pdCompletionCommRing L p (jL d)
  let := pdCompletionCommRing M p (jM (e d))
  rw [deltaDivisionFrobeniusCompletedResidueEquiv, Ideal.quotientEquiv_mk]
  congr 1
  exact deltaDivisionCoefficientPDCompletionEquiv_coeff D (D.frobeniusEquiv hD)
    (D.frobeniusEquiv_isDeltaHom hD) d a b

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionFrobeniusCompletedResidue

/-! ## Frobenius 側の実完備化剰余を raw 剰余へ戻す

## 概要

完全 δ 環上の raw 包の実完備化後の (d,φ⁻¹(d)) 商は、
Frobenius 側の未完備 raw 包の (p,d) 商と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余計算の一段。

## 方針

φ(d) が (p,d) に属すことを使い、実完備化側の二元剰余比較の後に
両完備化座標を殺す商の普遍性による同型を合成する。

## 規約

実 H⁰ と標準単位を保持し、raw 剰余と pd 包の同定はまだ含めない。

## 使われ方

完備化後の Frobenius 比較を、通常代数として計算する raw 剰余へ接続する。
-/

@[expose] public noncomputable section DeltaDivisionFrobeniusCompletionToRaw

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (a : σ → A)
local notation "φ" => D.frobeniusLift
local notation "e" => DeltaStructure.frobeniusEquiv D hD
local notation "x" => RingEquiv.symm (DeltaStructure.frobeniusEquiv D hD) d
local notation "L" => DeltaAdjoinDivision D d a
local notation "M" => DeltaAdjoinDivision D (e d) (fun s => e (a s))
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "jM" => deltaAdjoinDivisionMap D (e d) (fun s => e (a s))
local notation "HL" => PDCompletionH0 L p (jL d)
local notation "uL" => pdCompletionUnit L p (jL d)

/-- 概要：Frobenius 側の実完備化の第二座標は raw 包の (p,d) イデアルに属す。
方針：φ(d)=d^p+pδ(d) の各項の所属を係数射で送る。
規約：d の distinguished 性はこの所属計算には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化座標を殺す商比較への入力。 -/
theorem deltaDivisionFrobeniusCompletionCoordinate_mem :
    jM (e d) ∈ Ideal.span {(p : M), jM d} := by
  have hd : d ∈ Ideal.span {(p : A), d} := Ideal.subset_span (by simp)
  have hp : (p : A) ∈ Ideal.span {(p : A), d} := Ideal.subset_span (by simp)
  have hφ : φ d ∈ Ideal.span {(p : A), d} := by
    rw [D.frobeniusLift_apply]
    exact (Ideal.span {(p : A), d}).add_mem
      ((Ideal.span {(p : A), d}).pow_mem_of_mem hd p (Nat.Prime.pos (Fact.out : p.Prime)))
      ((Ideal.span {(p : A), d}).mul_mem_right _ hp)
  have h := Ideal.mem_map_of_mem jM hφ
  change jM (D.frobeniusLift d) ∈ Ideal.span {(p : M), jM d}
  simpa only [Ideal.map_span, Set.image_pair, map_natCast] using h

/-- 概要：元の raw 包の実完備化後の剰余は Frobenius 側の未完備 raw 剰余と環同型。
方針：実完備化後の Frobenius 同型と、両座標を殺す二元商の比較を合成する。
規約：係数 δ 環は完全、d は distinguished とする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包へ進む未完備剰余への接続。 -/
def deltaDivisionFrobeniusCompletionToRawEquiv (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing L p (jL d)
    (HL ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+*
      (M ⧸ Ideal.span {(p : M), jM d}) := by
  let := pdCompletionCommRing L p (jL d)
  let := pdCompletionCommRing M p (jM (e d))
  exact (deltaDivisionFrobeniusCompletedResidueEquiv D hD d a hd).trans
    (pdCompletionPairResidueEquiv p (jM (e d)) (jM d)
      (deltaDivisionFrobeniusCompletionCoordinate_mem D hD d a))

/-- 概要：実完備化から raw 剰余への比較は係数 b を φ(b) の剰余へ送る。
方針：完備化後の Frobenius 係数公式と二元剰余比較の単位公式を使う。
規約：元の係数射と実完備化単位を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包へ接続する係数作用。 -/
theorem deltaDivisionFrobeniusCompletionToRawEquiv_coeff
    (hd : D.IsDistinguished d) (b : A) :
    letI := pdCompletionCommRing L p (jL d)
    deltaDivisionFrobeniusCompletionToRawEquiv D hD d a hd
      (Ideal.Quotient.mk _ (uL (jL b))) = Ideal.Quotient.mk _ (jM (φ b)) := by
  let := pdCompletionCommRing L p (jL d)
  let := pdCompletionCommRing M p (jM (e d))
  rw [deltaDivisionFrobeniusCompletionToRawEquiv, RingEquiv.trans_apply,
    deltaDivisionFrobeniusCompletedResidueEquiv_coeff, pdCompletionPairResidueEquiv_unit]

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionFrobeniusCompletionToRaw

/-! ## 実完備化の剰余を raw p 除算剰余へ接続

## 概要

完全 δ 環の distinguished d に対し、A{a/d} の実完備化後の
(d,φ⁻¹(d)) 商を A{φ(a)/p}/(p,d) と環同型にする。
BS 著者版 Remark 7.15（著者版 p.62）の具体的 pd 包比較への接続。

## 方針

実完備化から Frobenius 側 raw 剰余への同型に、Witt 単元による分母変換を合成する。

## 規約

実 H⁰ とその標準単位を維持する。原典とは異なる Witt 座標による証明である。

## 使われ方

既存の raw p 除算包と pd 表示との比較へ、実完備化の剰余を渡す。
-/

@[expose] public noncomputable section DeltaDivisionCompletionPResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) (a : σ → A)
local notation "L" => DeltaAdjoinDivision D d a
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "H" => PDCompletionH0 L p (jL d)
local notation "uL" => pdCompletionUnit L p (jL d)
local notation "x" => RingEquiv.symm (DeltaStructure.frobeniusEquiv D hD) d
local notation "b" => fun s => D.frobeniusLift (a s)
local notation "Qp" => DeltaDivisionPairResidue D (p : A) b d

/-- 概要：実完備化後の二元剰余は Frobenius 分子の raw p 除算剰余と環同型。
方針：実完備化から raw への比較に、Witt 単元による分母変換を合成する。
規約：完全 δ 環、distinguished d、源の p 正則性と ghost 単射性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化から具体的 pd 包への接続。 -/
def deltaDivisionCompletionPResidueEquiv :
    letI := pdCompletionCommRing L p (jL d)
    (H ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+* Qp := by
  let := pdCompletionCommRing L p (jL d)
  exact (deltaDivisionFrobeniusCompletionToRawEquiv D hD d a hd).trans
    (deltaDivisionFrobeniusPResidueEquiv D hpA hgA hgL d hd b)

/-- 概要：実完備化から raw p 剰余への同型は係数 r を φ(r) の剰余へ送る。
方針：Frobenius 比較の係数公式と分母変換の係数保存を使う。
規約：元の標準完備化単位を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 引戻しの係数作用を追う。 -/
theorem deltaDivisionCompletionPResidueEquiv_coeff (r : A) :
    letI := pdCompletionCommRing L p (jL d)
    deltaDivisionCompletionPResidueEquiv D hpA hgA hgL hD d hd a
        (Ideal.Quotient.mk _ (uL (jL r))) =
      deltaDivisionPairResidueBase D (p : A) b d (D.frobeniusLift r) := by
  let := pdCompletionCommRing L p (jL d)
  rw [deltaDivisionCompletionPResidueEquiv, RingEquiv.trans_apply,
    deltaDivisionFrobeniusCompletionToRawEquiv_coeff]
  exact deltaDivisionFrobeniusPResidueEquiv_base D hpA hgA hgL d hd b (D.frobeniusLift r)

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionCompletionPResidue

/-! ## 実完備化の二元剰余と標準主 pd 表示

## 概要

完全 δ 環上の一元 raw 包 A{y/d} の実完備化後の (d,φ⁻¹(d)) 商は、
A/(p,d) 上の y の標準主分冪表示と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の具体的な pd 台環の比較。

## 方針

実完備化剰余を raw φ(y)/p 剰余へ移し、既存の階乗計算と係数イデアル商を合成する。

## 規約

源の完全性・p 正則性・p 局所性、d の distinguished 性、y mod p の正則性を明示する。
原典とは異なる Witt 座標による証明。prismatic 源との同定は別工程。

## 使われ方

無限根多項式環上のモニック入力へ適用して原典の具体的 pd 包へ接続する。
-/

@[expose] public noncomputable section DeltaDivisionCompletionPrincipalPD

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun r : A => (p : A) * r))
variable (D : DeltaStructure p A) (hD : D.IsPerfect)
variable (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (hd : D.IsDistinguished d) (y : A)
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "a" => fun _ : σ => y
local notation "L" => DeltaAdjoinDivision D d a
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "H" => PDCompletionH0 L p (jL d)
local notation "uL" => pdCompletionUnit L p (jL d)
local notation "x" => RingEquiv.symm (DeltaStructure.frobeniusEquiv D hD) d
local notation "K" => Ideal.span {(p : A), d}
local notation "R" => A ⧸ K
local notation "bar" => Ideal.Quotient.mk K

/-- 概要：実完備化後の一元 raw 剰余は係数二元商上の標準主分冪表示と環同型。
方針：Frobenius と Witt 分母変換による比較に raw-pd 係数商同型を合成する。
規約：仮定は源と入力の正則性・局所性・完全性であり、比較同型自体は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化の剰余の具体的 pd 表示。 -/
def deltaDivisionCompletionPrincipalPDEquiv :
    letI := pdCompletionCommRing L p (jL d)
    (H ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+* PrincipalDPPresentation R (bar y) := by
  let := pdCompletionCommRing L p (jL d)
  exact (deltaDivisionCompletionPResidueEquiv D hpA hgA hgL hD d hd a).trans
    (deltaPDivisionPairPDEquiv hA hpA D y hgL v hv hy d)

/-- 概要：実完備化の pd 台環比較は係数 r を φ(r) の剰余係数へ送る。
方針：実完備化から raw への係数公式と raw-pd の係数保存を使う。
規約：実完備化単位と元の係数射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 引戻しを係数上で照合する。 -/
theorem deltaDivisionCompletionPrincipalPDEquiv_coeff (r : A) :
    letI := pdCompletionCommRing L p (jL d)
    deltaDivisionCompletionPrincipalPDEquiv hA hpA D hD hgA hgL d hd y v hv hy
        (Ideal.Quotient.mk _ (uL (jL r))) =
      algebraMap R (PrincipalDPPresentation R (bar y)) (bar (D.frobeniusLift r)) := by
  let := pdCompletionCommRing L p (jL d)
  rw [deltaDivisionCompletionPrincipalPDEquiv, RingEquiv.trans_apply,
    deltaDivisionCompletionPResidueEquiv_coeff]
  exact deltaPDivisionPairPDEquiv_coeff hA hpA D y hgL v hv hy d (D.frobeniusLift r)

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionCompletionPrincipalPD

/-! ## 有限 mod p 関係商での次関係の正則性

## 概要

有限 δ 関係商の mod p で d が正則なら、次の δ 関係もそこで正則。
BS 著者版 Remark 7.15（著者版 p.62）の p 正則性の同時帰納法への次段の入力。

## 方針

最高係数 φ^(N+1)(d) を d の正冪と計算し、有限変数分離後の一次式に適用する。

## 規約

d の正則性を保つ帰納法そのものは別工程。完備化の離散性をここでは結論しない。

## 使われ方

有限 raw 包の p 正則性を正則列の順序交換で保つ。
-/

@[expose] public noncomputable section DeltaDivisionFiniteModPrimeRegularity

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：正則な先頭係数を持つ一次多項式は正則。
方針：最高係数による多項式の非零因子判定を使う。
規約：係数環が零環の場合も含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の次 δ 関係の線形表示。 -/
theorem linearPolynomial_regular {R : Type u} [CommRing R] (c b : R)
    (hc : IsSMulRegular R c) :
    IsSMulRegular (Polynomial R) (Polynomial.C c * Polynomial.X + Polynomial.C b) := by
  change Function.Injective (fun x : Polynomial R =>
    (Polynomial.C c * Polynomial.X + Polynomial.C b) * x)
  nontriviality R
  have hc₀ : c ≠ 0 := by
    intro h
    have he : c * (1 : R) = c * 0 := by simp [h]
    exact one_ne_zero (hc he)
  have hp : (Polynomial.C c * Polynomial.X + Polynomial.C b) ∈
      nonZeroDivisors (Polynomial R) := by
    apply Polynomial.mem_nonZeroDivisors_of_leadingCoeff
    rw [Polynomial.leadingCoeff_linear hc₀]
    exact mem_nonZeroDivisors_iff_left.mpr fun x hx => hc (hx.trans (mul_zero c).symm)
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hp).left

/-- 概要：指定変数の正則係数一次式は多変数多項式環でも正則。
方針：指定変数を一変数として分離し、残りの変数の平坦性を使う。
規約：変数族は任意。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限商後の次関係。 -/
theorem linearMvPolynomial_regular {R : Type u} [CommRing R] {τ : Type v}
    (c b : R) (s : τ) (hc : IsSMulRegular R c) :
    IsSMulRegular (MvPolynomial τ R) (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : τ // t ≠ s})
  have he : e (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) =
      Polynomial.C (MvPolynomial.C c) * Polynomial.X + Polynomial.C (MvPolynomial.C b) := by
    simp [e, MvPolynomial.renameEquiv]
  have hc' := hc.of_flat (S := MvPolynomial {t : τ // t ≠ s} R)
  have hr := linearPolynomial_regular (MvPolynomial.C c) (MvPolynomial.C b) hc'
  intro x y h
  apply e.injective
  apply hr
  have hh := congrArg e h
  simpa only [smul_eq_mul, map_mul, he] using hh

/-- 概要：正則対 c,b の線形除算関係 cX-b を課しても c は正則。
方針：mod c で関係が -b になることを使い、正則対の順序交換を適用する。
規約：c は係数環で正則、b は mod c で正則とする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最初の δ 関係商で d を保つ計算。 -/
theorem linearMvPolynomial_coefficient_regular_quotient
    {R : Type u} [CommRing R] {τ : Type v} (c b : R) (s : τ)
    (hc : IsSMulRegular R c)
    (hb : IsSMulRegular (R ⧸ Ideal.span {c}) (Ideal.Quotient.mk (Ideal.span {c}) b)) :
    IsSMulRegular (MvPolynomial τ R ⧸
      Ideal.span {MvPolynomial.C c * MvPolynomial.X s - MvPolynomial.C b})
      (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.C c * MvPolynomial.X s - MvPolynomial.C b})
        (MvPolynomial.C c)) := by
  let T := MvPolynomial τ R
  let g : T := MvPolynomial.C c * MvPolynomial.X s - MvPolynomial.C b
  let q := Ideal.Quotient.mk (Ideal.span {(MvPolynomial.C c : T)})
  have hcT : IsSMulRegular T (MvPolynomial.C c) := hc.of_flat (S := T)
  have hbT : IsSMulRegular (T ⧸ Ideal.span {(MvPolynomial.C c : T)})
      (q (MvPolynomial.C b)) :=
    SerrePositivity.isSMulRegular_mod_of_flat c b hc hb
  have hg : q g = -q (MvPolynomial.C b) := by
    change q (MvPolynomial.C c * MvPolynomial.X s - MvPolynomial.C b) = _
    rw [map_sub, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), zero_mul, zero_sub]
  apply principal_regular_swap (MvPolynomial.C c : T) g hcT
  rw [hg]
  intro x y hxy
  apply hbT
  simpa only [neg_smul, neg_inj] using hxy

/-- 概要：p を殺す通常環射では反復 Frobenius は対応する p 冪。
方針：φ(r)=r^p+pδ(r) の像を帰納的に計算する。
規約：終域の δ 構造や非零性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の次関係の最高係数の正則性。 -/
theorem deltaFrobeniusIterate_map_of_prime_zero
    {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
    (D : DeltaStructure p A) (q : A →+* B) (hpq : q (p : A) = 0) (d : A) (n : ℕ) :
    q (D.frobeniusLift^[n] d) = q d ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', D.frobeniusLift_apply, map_add, map_pow,
      map_mul, hpq, zero_mul, add_zero, ih, ← pow_mul, Nat.pow_succ]

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a N
local notation "B₀" => MvPolynomial (σ × Fin (N + 1)) A
local notation "J₀" => deltaDivisionFiniteStageInitialIdeal D d a N
local notation "Jp" => Ideal.span {(p : B₀)} ⊔ J₀
local notation "Ip" => Ideal.span {(p : L₀)} ⊔ I₀
local notation "e" => deltaDivisionFiniteModPrimeTailEquiv D d a N

/-- 概要：全自由環の有限 mod p 商での係数の正則性は初期係数商へ降りる。
方針：変数分離と係数多項式射の単射性を使う。
規約：元の A 係数 r を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最高係数の冪の正則性。 -/
theorem deltaDivisionFiniteModPrimeInitial_coefficient_regular (r : A)
    (hr : IsSMulRegular (L₀ ⧸ Ip) (Ideal.Quotient.mk Ip (MvPolynomial.C r))) :
    IsSMulRegular (B₀ ⧸ Jp) (Ideal.Quotient.mk Jp (MvPolynomial.C r)) := by
  have hr' : IsSMulRegular (MvPolynomial (σ × ℕ) (B₀ ⧸ Jp))
      (MvPolynomial.C (σ := σ × ℕ) (Ideal.Quotient.mk Jp (MvPolynomial.C r))) := by
    intro x y hxy
    apply (e).symm.injective
    apply hr
    apply (e).injective
    simpa only [map_mul, smul_eq_mul, RingEquiv.apply_symm_apply,
      deltaDivisionFiniteModPrimeTailEquiv_coeff] using hxy
  intro x y hxy
  apply (MvPolynomial.C_injective (σ := σ × ℕ))
  apply hr'
  simpa only [smul_eq_mul, map_mul] using
    congrArg (MvPolynomial.C : (B₀ ⧸ Jp) →+* MvPolynomial (σ × ℕ) (B₀ ⧸ Jp)) hxy

/-- 概要：mod p の有限関係商で d が正則なら次の δ 関係も正則。
方針：初期商の先頭係数を d の正冪と同定し、後続変数の一次式へ適用する。
規約：帰納法の入力である d の mod p 正則性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限 raw 関係商の p 正則性。 -/
theorem deltaDivisionFiniteModPrime_next_regular
    (hd : IsSMulRegular (L₀ ⧸ Ip) (Ideal.Quotient.mk Ip (MvPolynomial.C d))) (s : σ) :
    IsSMulRegular (L₀ ⧸ Ip)
      (Ideal.Quotient.mk Ip (deltaDivisionIteratedRelation D d a s (N + 1))) := by
  have hd' := deltaDivisionFiniteModPrimeInitial_coefficient_regular D d a N d hd
  let q : A →+* B₀ ⧸ Jp := (Ideal.Quotient.mk Jp).comp MvPolynomial.C
  have hpq : q (p : A) = 0 := by
    change Ideal.Quotient.mk Jp (MvPolynomial.C (p : A)) = 0
    rw [map_natCast]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {(p : B₀)} ≤ Jp from le_sup_left) (Ideal.mem_span_singleton_self _))
  have hc : IsSMulRegular (B₀ ⧸ Jp)
      (Ideal.Quotient.mk Jp (MvPolynomial.C (D.frobeniusLift^[N + 1] d))) := by
    change IsSMulRegular (B₀ ⧸ Jp) (q (D.frobeniusLift^[N + 1] d))
    rw [deltaFrobeniusIterate_map_of_prime_zero D q hpq]
    exact hd'.pow _
  have hreg := linearMvPolynomial_regular
    (Ideal.Quotient.mk Jp (MvPolynomial.C (D.frobeniusLift^[N + 1] d)))
    (Ideal.Quotient.mk Jp (deltaDivisionFiniteLeadingLowerPolynomial D d a s (N + 1))) (s, 0) hc
  intro x y hxy
  apply (e).injective
  apply hreg
  simpa only [smul_eq_mul, map_mul, deltaDivisionFiniteModPrimeTailEquiv_next] using congrArg e hxy

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionFiniteModPrimeRegularity

/-! ## 有限 δ 関係商の二重剰余と標準一重商

## 概要

有限 raw 関係商の mod p、さらに mod d を、元の自由環の対応する一重商へ移す。
一元族で次関係を課す商も次の有限段と同定する。
BS 著者版 Remark 7.15（著者版 p.62）の正則性の帰納法に用いる。

## 方針

通常商の第三同型定理を使い、全ての代表元の像を保持する。

## 規約

正則性・完備性を仮定しない通常環同型。

## 使われ方

次段の正則性と既存の mod(p,d) Witt 計算を同じ有限商へ移す。
-/

@[expose] public noncomputable section DeltaDivisionFinitePrimeQuotients

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：イデアル商に主関係を追加する二重商は和イデアル商と環同型。
方針：生成イデアルを像イデアルに書き換え第三同型定理を使う。
規約：元の代表元を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限関係追加と係数商。 -/
def idealThenPrincipalQuotEquiv {R : Type u} [CommRing R] (I : Ideal R) (r : R) :
    ((R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I r}) ≃+* R ⧸ (I ⊔ Ideal.span {r}) :=
  (Ideal.quotEquivOfEq (show Ideal.span {Ideal.Quotient.mk I r} =
    (Ideal.span {r}).map (Ideal.Quotient.mk I) by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {r}))

/-- 概要：主関係を追加する商同型は元の代表元を保つ。
方針：第三同型定理の代表元公式を使う。
規約：任意のイデアルと関係元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限段の係数照合。 -/
theorem idealThenPrincipalQuotEquiv_mk {R : Type u} [CommRing R]
    (I : Ideal R) (r t : R) :
    idealThenPrincipalQuotEquiv I r (Ideal.Quotient.mk _ (Ideal.Quotient.mk I t)) =
      Ideal.Quotient.mk _ t := by
  rw [idealThenPrincipalQuotEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I (Ideal.span {r}) t

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I" => deltaDivisionFiniteRelationIdeal D d a N
local notation "B" => L₀ ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "qp" => Ideal.Quotient.mk (Ideal.span {(p : B)})
local notation "Ip" => Ideal.span {(p : L₀)} ⊔ I
local notation "Ipd" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔ I

/-- 概要：有限関係商の通常 mod p は元の自由環の (p)+I_N 商と環同型。
方針：自然数の像を照合して主関係追加の同型を使う。
規約：一重商は既存の有限 mod p 分離と同じイデアル順序にする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の次関係正則性の移送。 -/
def deltaDivisionFiniteStagePrimeQuotientEquiv : (B ⧸ Ideal.span {(p : B)}) ≃+* L₀ ⧸ Ip :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : B)} = Ideal.span {q (p : L₀)} by
    rw [map_natCast])).trans
    ((idealThenPrincipalQuotEquiv I (p : L₀)).trans (Ideal.quotEquivOfEq (sup_comm _ _)))

/-- 概要：有限段の mod p 比較は元の自由環の代表元を保つ。
方針：主関係追加同型の公式を使う。
規約：全ての自由環元 t を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数と次関係の照合。 -/
theorem deltaDivisionFiniteStagePrimeQuotientEquiv_mk (t : L₀) :
    deltaDivisionFiniteStagePrimeQuotientEquiv D d a N (qp (q t)) = Ideal.Quotient.mk Ip t := by
  rw [deltaDivisionFiniteStagePrimeQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply,
    idealThenPrincipalQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

local notation "Ep" => deltaDivisionFiniteStagePrimeQuotientEquiv D d a N

/-- 概要：有限関係商の mod p,d 二重剰余は既存の一重 mod(p,d) 商と環同型。
方針：mod p 比較を d の商へ降ろし、和イデアルを整理する。
規約：Witt 正規化と同じ一重イデアル商を対象にする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の次関係の mod d 正則性の移送。 -/
def deltaDivisionFiniteStagePairQuotientEquiv :
    ((B ⧸ Ideal.span {(p : B)}) ⧸ Ideal.span {qp (q (MvPolynomial.C d))}) ≃+* L₀ ⧸ Ipd :=
  ((Ideal.quotientEquiv _ _ Ep (show
    Ideal.span {Ideal.Quotient.mk Ip (MvPolynomial.C d)} =
      (Ideal.span {qp (q (MvPolynomial.C d))}).map (Ep).toRingHom by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1)).trans
    (idealThenPrincipalQuotEquiv Ip (MvPolynomial.C d))).trans
      (Ideal.quotEquivOfEq (show Ip ⊔ Ideal.span {MvPolynomial.C d} = Ipd by
        rw [Ideal.span_insert]
        ac_rfl))

/-- 概要：有限段の mod p,d 比較は元の自由環の代表元を保つ。
方針：商への降下と主関係追加の二つの代表元公式を使う。
規約：三つの実商射をそのまま用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 δ 関係の正則性の照合。 -/
theorem deltaDivisionFiniteStagePairQuotientEquiv_mk (t : L₀) :
    deltaDivisionFiniteStagePairQuotientEquiv D d a N (Ideal.Quotient.mk _ (qp (q t))) =
      Ideal.Quotient.mk Ipd t := by
  rw [deltaDivisionFiniteStagePairQuotientEquiv, RingEquiv.trans_apply,
    RingEquiv.trans_apply, Ideal.quotientEquiv_mk, deltaDivisionFiniteStagePrimeQuotientEquiv_mk,
    idealThenPrincipalQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

variable [Unique σ]
local notation "g" => deltaDivisionIteratedRelation D d a (default : σ)

/-- 概要：一元族の深さ零の関係イデアルは初期関係の主イデアル。
方針：唯一の族添字と唯一の深さ零添字を照合する。
規約：分母 d と分子族 a は任意。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正則性帰納法の初期段。 -/
theorem deltaDivisionUnaryFiniteIdeal_zero :
    deltaDivisionFiniteRelationIdeal D d a 0 = Ideal.span {g 0} := by
  unfold deltaDivisionFiniteRelationIdeal
  congr 1
  ext z
  constructor
  · rintro ⟨⟨s, n⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    have hn : n = 0 := Fin.ext (by omega)
    subst s
    subst n
    exact Set.mem_singleton _
  · rintro rfl
    exact ⟨((default : σ), 0), rfl⟩

/-- 概要：一元族の次有限段は一つの次 δ 関係を追加して得る。
方針：既存の族の和イデアル式で唯一の添字を照合する。
規約：任意の深さ N。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正則性の次段への移送。 -/
theorem deltaDivisionUnaryFiniteIdeal_succ :
    deltaDivisionFiniteRelationIdeal D d a (N + 1) = I ⊔ Ideal.span {g (N + 1)} := by
  rw [deltaDivisionFiniteRelationIdeal_succ]
  congr 1
  congr 1
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact Set.mem_singleton _
  · rintro rfl
    exact ⟨default, rfl⟩

/-- 概要：一元の次関係商は元の次有限段と環同型。
方針：主関係追加の同型と次段イデアルの等式を合成する。
規約：完備化を行わない通常商の同型。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正則対の帰納法。 -/
def deltaDivisionUnaryFiniteStepEquiv :
    (B ⧸ Ideal.span {q (g (N + 1))}) ≃+*
      L₀ ⧸ deltaDivisionFiniteRelationIdeal D d a (N + 1) :=
  (idealThenPrincipalQuotEquiv I (g (N + 1))).trans
    (Ideal.quotEquivOfEq (deltaDivisionUnaryFiniteIdeal_succ D d a N).symm)

/-- 概要：次有限段の比較は元の自由環の代表元を保つ。
方針：主関係追加同型の代表元公式を使う。
規約：元の自由環の全ての元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数正則性の移送。 -/
theorem deltaDivisionUnaryFiniteStepEquiv_mk (t : L₀) :
    deltaDivisionUnaryFiniteStepEquiv D d a N (Ideal.Quotient.mk _ (q t)) =
      Ideal.Quotient.mk _ t := by
  rw [deltaDivisionUnaryFiniteStepEquiv, RingEquiv.trans_apply,
    idealThenPrincipalQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionFinitePrimeQuotients

/-! ## 有限 δ 関係商の p,d 正則性を次段へ保つ

## 概要

一元 raw 包の有限段で p が正則、mod p で d が正則なら、次段でも両条件が成り立つ。
BS 著者版 Remark 7.15（著者版 p.62）の源の p 正則性の帰納法。

## 方針

最高係数の正則性で次関係は mod p で正則。
既存 Witt 計算で mod(p,d) でも正則なので、正則対の順序交換を二度使う。

## 規約

源の p 正則性、自由 δ 環の ghost 単射性、δ(d) の単元性を明示する。
初期段の正則性を仮定する次段の定理であり、全有限段への帰納法は別工程。

## 使われ方

無限根モニック入力の初期正則対を全有限 δ 関係商へ移す。
-/

@[expose] public noncomputable section DeltaDivisionFiniteRegularStep

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun r : A => (p : A) * r))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I" => deltaDivisionFiniteRelationIdeal D d a N
local notation "B" => L₀ ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "qp" => Ideal.Quotient.mk (Ideal.span {(p : B)})
local notation "dN" => q (MvPolynomial.C d)
local notation "g" => deltaDivisionIteratedRelation D d a (default : σ) (N + 1)
local notation "gN" => q g
local notation "Ip" => Ideal.span {(p : L₀)} ⊔ I
local notation "Ipd" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔ I
local notation "I'" => deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "B'" => L₀ ⧸ I'
local notation "q'" => Ideal.Quotient.mk I'

include hpA hgL hv in
/-- 概要：有限段の次関係は mod p,d の通常二重商上で正則。
方針：最初の δ 関係とそれ以降の既存 Witt 正則性を場合分けして移す。
規約：前段の p,d 正則性はこの mod(p,d) 計算には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正則対の次段への移送。 -/
theorem deltaDivisionUnaryFinite_next_mod_pair_regular :
    IsSMulRegular ((B ⧸ Ideal.span {(p : B)}) ⧸ Ideal.span {qp dN})
      (Ideal.Quotient.mk (Ideal.span {qp dN}) (qp gN)) := by
  have hr : IsSMulRegular (L₀ ⧸ Ipd) (Ideal.Quotient.mk Ipd g) := by
    cases N with
    | zero => exact deltaDivisionFirstJet_residue_isSMulRegular D d a v hv default
    | succ n =>
      have hpL : Function.Injective (fun r : L₀ => (p : L₀) * r) := by
        simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
          (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
      exact deltaDivisionFiniteNextJet_quotient_isSMulRegular D hpA hpL hgL d a v hv n default
  let e := deltaDivisionFiniteStagePairQuotientEquiv D d a N
  apply (ringEquiv_isSMulRegular e _).mpr
  rw [deltaDivisionFiniteStagePairQuotientEquiv_mk]
  exact hr

/-- 概要：d が有限段の mod p で正則なら次関係も同じ mod p で正則。
方針：一重商で証明した次関係の正則性を標準 mod p 商同型で戻す。
規約：d の正則性を次段帰納法の入力とする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の p 正則性の保存。 -/
theorem deltaDivisionUnaryFinite_next_mod_prime_regular
    (hd : IsSMulRegular (B ⧸ Ideal.span {(p : B)}) (qp dN)) :
    IsSMulRegular (B ⧸ Ideal.span {(p : B)}) (qp gN) := by
  let e := deltaDivisionFiniteStagePrimeQuotientEquiv D d a N
  have hd' := (ringEquiv_isSMulRegular e (qp dN)).mp hd
  rw [deltaDivisionFiniteStagePrimeQuotientEquiv_mk] at hd'
  have hr := deltaDivisionFiniteModPrime_next_regular D d a N hd' default
  apply (ringEquiv_isSMulRegular e _).mpr
  rw [deltaDivisionFiniteStagePrimeQuotientEquiv_mk]
  exact hr

include hpA hgL hv in
/-- 概要：一元有限関係商の p 正則性と mod p の d 正則性は次段へ保存される。
方針：次関係の mod p と mod(p,d) 正則性で三元の正則性保存を使う。
規約：前段の二つの正則性は明示仮定。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全有限段への同時帰納法。 -/
theorem deltaDivisionUnaryFinite_step_regular
    (hpN : IsSMulRegular B (p : B))
    (hdN : IsSMulRegular (B ⧸ Ideal.span {(p : B)}) (qp dN)) :
    IsSMulRegular B' (p : B') ∧
      IsSMulRegular (B' ⧸ Ideal.span {(p : B')})
        (Ideal.Quotient.mk (Ideal.span {(p : B')}) (q' (MvPolynomial.C d))) := by
  have hgN := deltaDivisionUnaryFinite_next_mod_prime_regular D d a N hdN
  have hgdN := deltaDivisionUnaryFinite_next_mod_pair_regular D hpA hgL d a v hv N
  have hstep := regularTripleQuotientStep (p : B) dN gN hpN hdN hgN hgdN
  let e := deltaDivisionUnaryFiniteStepEquiv D d a N
  have hpQ : IsSMulRegular (B ⧸ Ideal.span {gN}) (p : B ⧸ Ideal.span {gN}) := by
    simpa only [map_natCast] using hstep.1
  have hdQ : IsSMulRegular ((B ⧸ Ideal.span {gN}) ⧸
      Ideal.span {(p : B ⧸ Ideal.span {gN})})
      (Ideal.Quotient.mk (Ideal.span {(p : B ⧸ Ideal.span {gN})})
        (Ideal.Quotient.mk (Ideal.span {gN}) dN)) := by
    let C := B ⧸ Ideal.span {gN}
    let j : B →+* C := Ideal.Quotient.mk _
    have aux (c : C) (hc : c = (p : C))
        (hr : IsSMulRegular (C ⧸ Ideal.span {c})
          (Ideal.Quotient.mk (Ideal.span {c}) (j dN))) :
        IsSMulRegular (C ⧸ Ideal.span {(p : C)})
          (Ideal.Quotient.mk (Ideal.span {(p : C)}) (j dN)) := by
      subst c
      exact hr
    exact aux _ (map_natCast j p) hstep.2
  refine ⟨?_, ?_⟩
  · have h := (ringEquiv_isSMulRegular e (p : B ⧸ Ideal.span {gN})).mp hpQ
    simpa only [map_natCast] using h
  · let ep : ((B ⧸ Ideal.span {gN}) ⧸ Ideal.span {(p : B ⧸ Ideal.span {gN})}) ≃+*
        (B' ⧸ Ideal.span {(p : B')}) :=
      Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton, map_natCast])
    have h := (ringEquiv_isSMulRegular ep _).mp hdQ
    have he : ep (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ dN)) =
        Ideal.Quotient.mk (Ideal.span {(p : B')}) (q' (MvPolynomial.C d)) := by
      rw [Ideal.quotientEquiv_mk, deltaDivisionUnaryFiniteStepEquiv_mk]
    rw [he] at h
    exact h

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionFiniteRegularStep

/-! ## raw Frobenius 係数変更と二つの剰余

## 概要

完全 δ 環の distinguished 元 d に対し、raw 包の (d,φ⁻¹(d)) 商は
Frobenius で移した raw 包の (p,d) 商と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の二重剰余の代数的比較。

## 方針

係数自己同型による raw 同型を二元イデアルの商へ降ろす。
φ(d)=d^p+pδ(d) と δ(d) の単元性で像イデアルを (p,d) と同定する。

## 規約

未完備の raw 包を扱う。これだけで原典の完備化済みの比較を主張しない。

## 使われ方

Hodge–Tate 商と ϖ 商に対応する二元イデアルを Frobenius の両側で追跡する。
-/

@[expose] public noncomputable section DeltaDivisionFrobeniusResidue

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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二重剰余への降下。 -/
theorem deltaDivisionCoefficientAut_pairIdeal (r s : A) :
    (Ideal.span {jL r, jL s}).map (F).toRingHom = Ideal.span {jM (e r), jM (e s)} := by
  rw [Ideal.map_span, Set.image_pair]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    deltaDivisionCoefficientAutEquiv_coeff]

/-- 概要：raw 係数自己同型は二元係数イデアルの実商の同型を誘導する。
方針：像イデアルの計算を標準商同型へ供給する。
規約：両側とも実際の span の商を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余台環の比較。 -/
def deltaDivisionCoefficientAutResidueEquiv (r s : A) :
    (L ⧸ Ideal.span {jL r, jL s}) ≃+* (M ⧸ Ideal.span {jM (e r), jM (e s)}) :=
  Ideal.quotientEquiv _ _ F (deltaDivisionCoefficientAut_pairIdeal D e he d a r s).symm

/-- 概要：raw 剰余比較は代表元を元の raw 同型で送る。
方針：商同型の標準代表元公式を使う。
規約：raw 包の任意の元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数・除算変数の照合。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二重剰余の標準化。 -/
theorem deltaDivisionFrobenius_pairIdeal (hd : D.IsDistinguished d) :
    Ideal.span {jφ (φ d), jφ (φ x)} = Ideal.span {(p : Mφ), jφ d} := by
  have hx : φ x = d := (D.frobeniusEquiv hD).apply_symm_apply d
  rw [hx]
  have h := congrArg (Ideal.map jφ) (distinguished_frobenius_pair_span D d hd)
  simpa only [Ideal.map_span, Set.image_pair, map_natCast] using h

/-- 概要：raw 包の (d,φ⁻¹(d)) 商は Frobenius 側の (p,d) 商と環同型。
方針：Frobenius の raw 同型を商へ降ろし、像の二元イデアルを標準化する。
規約：d は distinguished、係数 δ 環は完全とする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化前の二重剰余比較。 -/
def deltaDivisionFrobeniusResidueEquiv (hd : D.IsDistinguished d) :
    (L ⧸ Ideal.span {jL d, jL x}) ≃+* (Mφ ⧸ Ideal.span {(p : Mφ), jφ d}) :=
  (deltaDivisionCoefficientAutResidueEquiv D (D.frobeniusEquiv hD)
    (D.frobeniusEquiv_isDeltaHom hD) d a d x).trans
      (Ideal.quotEquivOfEq (deltaDivisionFrobenius_pairIdeal D d a hD hd))

/-- 概要：二重剰余比較は元の係数 b を Frobenius 係数 φ(b) へ送る。
方針：raw 係数公式と二つの商同型の代表元公式を使う。
規約：同型は元の A 係数に関して Frobenius 半線形。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の残余係数作用の追跡。 -/
theorem deltaDivisionFrobeniusResidueEquiv_coeff (hd : D.IsDistinguished d) (b : A) :
    deltaDivisionFrobeniusResidueEquiv D d a hD hd (Ideal.Quotient.mk _ (jL b)) =
      Ideal.Quotient.mk _ (jφ (φ b)) := by
  simp only [deltaDivisionFrobeniusResidueEquiv, RingEquiv.trans_apply,
    deltaDivisionCoefficientAutResidueEquiv_mk, deltaDivisionCoefficientAutEquiv_coeff]
  rfl

/-- 概要：二重剰余比較は初期除算変数の添字を保つ。
方針：raw 変数公式と商代表元公式を合成する。
規約：任意の入力族を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根関係の残余座標の追跡。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の T/ϖ に対応する代数的剰余。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の T/ϖ の係数作用の追跡。 -/
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

end DeltaDivisionFrobeniusResidue

/-! ## 最初の一元 raw 関係商の p,d 正則性

## 概要

係数環で p が正則、mod p で d が正則、mod(p,d) で分子が正則なら、
最初の線形除算関係を課した有限段でも p と mod p の d は正則。
BS 著者版 Remark 7.15（著者版 p.62）の有限段帰納法の初期値。

## 方針

mod p の自由多項式環へ係数変更し、正則な線形関係とその係数の正則性を使う。

## 規約

δ(d) の単元性は初期段には不要。完備化全体の正則性は別工程。

## 使われ方

無限根モニック入力の正則対を全有限 δ 関係商へ渡す。
-/

@[expose] public noncomputable section DeltaDivisionUnaryFiniteInitialRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "qp" => Ideal.Quotient.mk (Ideal.span {(p : L₀)})

/-- 概要：自由 δ 環の mod p は mod p 係数上の同じ自由多項式環。
方針：標準の多項式係数商同型で自然数の像を照合する。
規約：δ 構造を係数商に入れない通常環同型。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最初の線形関係の計算。 -/
def relativeFreeModPrimePolynomialEquiv :
    (L₀ ⧸ Ideal.span {(p : L₀)}) ≃+* MvPolynomial (σ × ℕ) R₀ :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : L₀)} =
    (Ideal.span {(p : A)}).map (MvPolynomial.C : A →+* L₀) by
      rw [Ideal.map_span, Set.image_singleton, map_natCast])).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := σ × ℕ) (Ideal.span {(p : A)})).symm.toRingEquiv

omit [Fact p.Prime] in
/-- 概要：自由環の mod p 同型は各多項式の係数だけを還元する。
方針：標準多項式商比較の合成公式を使う。
規約：全ての自由環元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数・初期関係の照合。 -/
theorem relativeFreeModPrimePolynomialEquiv_mk (t : L₀) :
    relativeFreeModPrimePolynomialEquiv (p := p) (A := A) (σ := σ) (qp t) =
      MvPolynomial.map bar t := by
  rw [relativeFreeModPrimePolynomialEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp (σ × ℕ) A
    (Ideal.span {(p : A)})) t

/-- 概要：最初の δ 関係の mod p 像は還元した係数による同じ線形関係。
方針：δ 反復の深さ零の定義と係数変更公式を使う。
規約：添字 s の初期変数を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の初期有限段の正則性。 -/
theorem relativeFreeModPrimePolynomialEquiv_first (s : σ) :
    relativeFreeModPrimePolynomialEquiv (p := p) (A := A) (σ := σ)
      (qp (deltaDivisionIteratedRelation D d a s 0)) =
        MvPolynomial.C (bar d) * MvPolynomial.X (s, 0) - MvPolynomial.C (bar (a s)) := by
  rw [relativeFreeModPrimePolynomialEquiv_mk]
  change MvPolynomial.map bar (MvPolynomial.C d * MvPolynomial.X (s, 0) -
    MvPolynomial.C (a s)) = _
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

variable [Unique σ]
local notation "g" => deltaDivisionIteratedRelation D d a (default : σ) 0
local notation "B" => L₀ ⧸ Ideal.span {g}
local notation "qg" => Ideal.Quotient.mk (Ideal.span {g})
local notation "G" => MvPolynomial.C (bar d) * MvPolynomial.X ((default : σ), 0) -
  MvPolynomial.C (bar (a default))
local notation "F" => relativeFreeModPrimePolynomialEquiv (p := p) (A := A) (σ := σ)

/-- 概要：最初の関係商の mod p は還元係数上の線形関係商と環同型。
方針：二重商を交換し、自由環の mod p 同型を線形関係の商へ降ろす。
規約：最初の実 δ 関係だけを課す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最初の商での d 正則性。 -/
def deltaDivisionUnaryFirstPrimeEquiv :
    (B ⧸ Ideal.span {(p : B)}) ≃+* (MvPolynomial (σ × ℕ) R₀ ⧸ Ideal.span {G}) :=
  ((Ideal.quotEquivOfEq (show Ideal.span {(p : B)} = Ideal.span {qg (p : L₀)} by
    rw [map_natCast])).trans (principalDoubleQuotSwapEquiv g (p : L₀))).trans
    (Ideal.quotientEquiv _ _ F (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
      congr 1
      exact (relativeFreeModPrimePolynomialEquiv_first D d a default).symm))

/-- 概要：最初の関係の mod p 比較は元の係数を還元した係数へ送る。
方針：二重商交換と自由環の mod p の代表元公式を使う。
規約：元の A の全係数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の初期係数正則性の移送。 -/
theorem deltaDivisionUnaryFirstPrimeEquiv_coeff (r : A) :
    deltaDivisionUnaryFirstPrimeEquiv D d a
      (Ideal.Quotient.mk _ (qg (MvPolynomial.C r))) =
        Ideal.Quotient.mk (Ideal.span {G}) (MvPolynomial.C (bar r)) := by
  rw [deltaDivisionUnaryFirstPrimeEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, principalDoubleQuotSwapEquiv_mk, Ideal.quotientEquiv_mk,
    relativeFreeModPrimePolynomialEquiv_mk, MvPolynomial.map_C]

/-- 概要：最初の実線形 δ 関係は mod p の自由環上で正則。
方針：係数 d の正則性から一次式の正則性を得て戻す。
規約：分子の正則性はこの非零因子判定には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の初期関係商の p 正則性。 -/
theorem deltaDivisionUnaryFirst_mod_prime_regular
    (hdA : IsSMulRegular R₀ (bar d)) :
    IsSMulRegular (L₀ ⧸ Ideal.span {(p : L₀)}) (qp g) := by
  apply (ringEquiv_isSMulRegular F _).mpr
  rw [relativeFreeModPrimePolynomialEquiv_first]
  simpa only [map_neg, sub_eq_add_neg] using
    linearMvPolynomial_regular (bar d) (-(bar (a default))) ((default : σ), 0) hdA

/-- 概要：最初の一元有限 δ 関係商は p 正則で、その mod p で d も正則。
方針：p と初期関係の順序交換、還元係数上の線形関係商の係数正則性を使う。
規約：係数環の正則対と分子の mod(p,d) 正則性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全有限段の同時帰納法の初期値。 -/
theorem deltaDivisionUnaryFirst_regular
    (hpA : IsSMulRegular A (p : A))
    (hdA : IsSMulRegular R₀ (bar d))
    (haA : IsSMulRegular (R₀ ⧸ Ideal.span {bar d})
      (Ideal.Quotient.mk (Ideal.span {bar d}) (bar (a default)))) :
    IsSMulRegular B (p : B) ∧
      IsSMulRegular (B ⧸ Ideal.span {(p : B)})
        (Ideal.Quotient.mk (Ideal.span {(p : B)}) (qg (MvPolynomial.C d))) := by
  refine ⟨?_, ?_⟩
  · have hpL : IsSMulRegular L₀ (p : L₀) := by
      simpa only [map_natCast] using hpA.of_flat (S := L₀)
    have h := principal_regular_swap (p : L₀) g hpL
      (deltaDivisionUnaryFirst_mod_prime_regular D d a hdA)
    simpa only [map_natCast] using h
  · let e := deltaDivisionUnaryFirstPrimeEquiv D d a
    apply (ringEquiv_isSMulRegular e _).mpr
    rw [deltaDivisionUnaryFirstPrimeEquiv_coeff]
    exact linearMvPolynomial_coefficient_regular_quotient (bar d) (bar (a default))
      ((default : σ), 0) hdA haA

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionUnaryFiniteInitialRegular

/-! ## 正則対上の一元 raw δ 除算包の p 正則性

## 概要

係数環の p,d と mod(p,d) の分子が正則で d が distinguished なら、
全有限関係商および一元 raw δ 除算包は p 正則。
BS 著者版 Remark 7.15（著者版 p.62）の無限根モニック入力の p 正則性への一般計算。

## 方針

初期段と次段の正則対保存を自然数で帰納し、有限関係イデアルの有向上限へ移す。

## 規約

p 完備性は要求しない。完備化後の p 正則性と prismatic 源の比較は別工程。

## 使われ方

完全 prism 上の無限根モニック raw 包へ補助仮定を具体的に供給して適用する。
-/

@[expose] public noncomputable section DeltaDivisionUnaryRawRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable (hpA : IsSMulRegular A (p : A))
variable (hdA : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) d))
variable (haA : IsSMulRegular ((A ⧸ Ideal.span {(p : A)}) ⧸
    Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) d})
  (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) d})
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (a default))))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta d)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I" => deltaDivisionFiniteRelationIdeal D d a
local notation "J" => DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
  (deltaDivisionRelationIdeal d a)
local notation "Raw" => DeltaAdjoinDivision D d a
include hpA hdA haA hgL hv

/-- 概要：全有限 δ 関係商で p と mod p の d は正則。
方針：初期線形関係商から、Witt 正則性による次段保存を帰納する。
規約：分子族は一元添字型上の任意の族。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 全体の p 飽和性への入力。 -/
theorem deltaDivisionUnaryFinite_all_regular (N : ℕ) :
    let B := L₀ ⧸ I N
    IsSMulRegular B (p : B) ∧
      IsSMulRegular (B ⧸ Ideal.span {(p : B)})
        (Ideal.Quotient.mk (Ideal.span {(p : B)})
          (Ideal.Quotient.mk (I N) (MvPolynomial.C d))) := by
  induction N with
  | zero =>
    let e : (L₀ ⧸ Ideal.span {deltaDivisionIteratedRelation D d a default 0}) ≃+* L₀ ⧸ I 0 :=
      Ideal.quotEquivOfEq (deltaDivisionUnaryFiniteIdeal_zero D d a).symm
    have h := deltaDivisionUnaryFirst_regular D d a hpA hdA haA
    have ht := ringEquiv_prime_pair_regular e p
      (Ideal.Quotient.mk _ (MvPolynomial.C d)) h.1 h.2
    simpa only [e, Ideal.quotEquivOfEq_mk] using ht
  | succ N ih =>
    exact deltaDivisionUnaryFinite_step_regular D hpA hgL d a v hv N ih.1 ih.2

/-- 概要：実 δ 関係イデアルは p で飽和している。
方針：有限関係イデアルの有向上限から一段へ降り、そこで p を消去する。
規約：全 δ 閉包を有限段で近似する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一元 raw 包の新しい p ねじれの排除。 -/
theorem deltaDivisionUnaryRaw_relationIdeal_p_saturated (f : L₀) (hf : (p : L₀) * f ∈ J) :
    f ∈ J := by
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations] at hf ⊢
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _
    (deltaDivisionFiniteRelationIdeal_mono D d a).directed_le).mp hf
  have hpN := (deltaDivisionUnaryFinite_all_regular D d a hpA hdA haA hgL v hv N).1
  have hz : Ideal.Quotient.mk (I N) f = 0 := by
    apply hpN
    change (p : L₀ ⧸ I N) * Ideal.Quotient.mk (I N) f = (p : L₀ ⧸ I N) * 0
    rw [mul_zero, ← map_natCast (Ideal.Quotient.mk (I N)) p, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hN
  exact (le_iSup I N) (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- 概要：正則対と正則分子を持つ一元 raw δ 除算包そのものは p 正則。
方針：係数商の p 飽和性を代表元へ適用する。
規約：ねじれを除く新しい商へ取り替えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化の前の p 正則性。 -/
theorem deltaDivisionUnaryRaw_p_mul_injective :
    Function.Injective (fun r : Raw => (p : Raw) * r) := by
  let q := Ideal.Quotient.mk J
  intro x z hxz
  change (p : Raw) * x = (p : Raw) * z at hxz
  apply sub_eq_zero.mp
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (x - z)
  have hpf : q ((p : L₀) * f) = 0 := by
    rw [map_mul, map_natCast, hf, mul_sub, hxz, sub_self]
  have hm := deltaDivisionUnaryRaw_relationIdeal_p_saturated D d a hpA hdA haA hgL v hv f
    (Ideal.Quotient.eq_zero_iff_mem.mp hpf)
  exact hf.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hm)

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionUnaryRawRegular

/-! ## 一元 raw δ 包の正則対

## 概要

有限 δ 関係商の mod p の分母正則性を、実 δ 閉包の商へ移す。
BS 著者版 Remark 7.15（著者版 p.62）の完備化前の正則対を提供する。

## 方針

(p) と有限関係イデアルの和も有向族となる。所属を一有限段へ降ろして分母を消去する。

## 規約

raw 包は元の δ 閉包商のままであり、完備化の正則性は別工程。

## 使われ方

実 (p,d) 完備化への正則対保存の入力。
-/

@[expose] public noncomputable section DeltaDivisionUnaryRawPairRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I" => deltaDivisionFiniteRelationIdeal D d a
local notation "J" => DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
  (deltaDivisionRelationIdeal d a)
local notation "Raw" => DeltaAdjoinDivision D d a
local notation "K" => Ideal.span {(p : L₀)} ⊔ J

/-- 概要：raw δ 包の通常 mod p は元の自由環の (p)+δ 閉包商と同型。
方針：主関係追加の第三同型定理を使う。
規約：正則性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限段から raw 包への比較。 -/
def deltaDivisionRawPrimeQuotientEquiv : (Raw ⧸ Ideal.span {(p : Raw)}) ≃+* L₀ ⧸ K :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : Raw)} =
    Ideal.span {Ideal.Quotient.mk J (p : L₀)} by rw [map_natCast])).trans
    ((idealThenPrincipalQuotEquiv J (p : L₀)).trans (Ideal.quotEquivOfEq (sup_comm _ _)))

/-- 概要：raw 包の mod p 比較は自由環の代表元を保つ。
方針：主関係追加の代表元公式を使う。
規約：全ての自由環元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母正則性の移送。 -/
theorem deltaDivisionRawPrimeQuotientEquiv_mk (t : L₀) :
    deltaDivisionRawPrimeQuotientEquiv D d a
      (Ideal.Quotient.mk (Ideal.span {(p : Raw)}) (Ideal.Quotient.mk J t)) =
        Ideal.Quotient.mk K t := by
  rw [deltaDivisionRawPrimeQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply, idealThenPrincipalQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

variable [Unique σ]
variable (hpA : IsSMulRegular A (p : A))
variable (hdA : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) d))
variable (haA : IsSMulRegular ((A ⧸ Ideal.span {(p : A)}) ⧸
    Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) d})
  (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) d})
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (a default))))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta d)
include hpA hdA haA hgL hv

/-- 概要：実 δ 関係イデアルに p を加えたイデアルは分母で飽和している。
方針：和と有向上限を交換し、一有限段の mod p の分母正則性で消去する。
規約：分母の係数像を元の自由環で扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 包の mod p 正則性。 -/
theorem deltaDivisionUnaryRaw_primeIdeal_d_saturated (t : L₀)
    (ht : MvPolynomial.C d * t ∈ K) : t ∈ K := by
  have hK : K = ⨆ N, Ideal.span {(p : L₀)} ⊔ I N := by
    rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations, sup_iSup]
  rw [hK] at ht ⊢
  have hmono : Monotone (fun N => Ideal.span {(p : L₀)} ⊔ I N) :=
    fun _ _ h => sup_le_sup_left (deltaDivisionFiniteRelationIdeal_mono D d a h) _
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp ht
  let e := deltaDivisionFiniteStagePrimeQuotientEquiv D d a N
  have hdN := (deltaDivisionUnaryFinite_all_regular D d a hpA hdA haA hgL v hv N).2
  have hreg : IsSMulRegular (L₀ ⧸ (Ideal.span {(p : L₀)} ⊔ I N))
      (Ideal.Quotient.mk (Ideal.span {(p : L₀)} ⊔ I N) (MvPolynomial.C d)) := by
    simpa only [e, deltaDivisionFiniteStagePrimeQuotientEquiv_mk] using
      (ringEquiv_isSMulRegular e _).mp hdN
  have hz : Ideal.Quotient.mk (Ideal.span {(p : L₀)} ⊔ I N) t = 0 := by
    apply hreg
    change Ideal.Quotient.mk _ (MvPolynomial.C d) * Ideal.Quotient.mk _ t = _ * 0
    rw [mul_zero, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hN
  exact (le_iSup (fun N => Ideal.span {(p : L₀)} ⊔ I N) N)
    (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- 概要：元の一元 raw δ 包の mod p で分母は正則。
方針：和イデアルの分母飽和性を代表元に適用し、標準比較で実 mod p へ戻す。
規約：完備性を要求せず、追加のねじれ除去商も作らない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化前の正則対の第二成分。 -/
theorem deltaDivisionUnaryRaw_mod_prime_d_regular :
    IsSMulRegular (Raw ⧸ Ideal.span {(p : Raw)})
      (Ideal.Quotient.mk (Ideal.span {(p : Raw)}) (Ideal.Quotient.mk J (MvPolynomial.C d))) := by
  apply (ringEquiv_isSMulRegular (deltaDivisionRawPrimeQuotientEquiv D d a) _).mpr
  rw [deltaDivisionRawPrimeQuotientEquiv_mk]
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ht : MvPolynomial.C d * t ∈ K := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, smul_eq_mul] using hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (deltaDivisionUnaryRaw_primeIdeal_d_saturated D d a hpA hdA haA hgL v hv t ht)

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionUnaryRawPairRegular

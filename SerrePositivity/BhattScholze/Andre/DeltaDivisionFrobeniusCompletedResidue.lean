module

public import SerrePositivity.BhattScholze.Andre.DeltaDivisionCoefficientPDCompletion
public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpi

/-!
# André E1・E2：実完備化後の Frobenius 比較と二重剰余

## 概要

完全 δ 環上の distinguished 元 d に対し、raw 包の実導来完備化を取った後の
(d,φ⁻¹(d)) 商は、Frobenius 側の実完備化後の (p,d) 商と環同型。
BS Rem 7.15（著者版 p.62）の Frobenius 比較の剰余への降下。

## 方針

実完備化同型の係数公式を使って二元イデアルの像を計算し、通常商同型へ降ろす。

## 規約

完備化と剰余の順序を交換する主張は含めない。実完備化 H⁰ を取った後の通常商を扱う。

## 使われ方

完備化済みの剰余と未完備 pd 包との後続比較に、係数作用を指定した同型を供給する。
-/

@[expose] public noncomputable section
universe u v
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
使われ方：BS Rem 7.15（著者版 p.62）の完備化後の剰余比較への入力。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の実完備化後の Frobenius 剰余比較。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の pd 包比較へ渡す係数作用。 -/
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

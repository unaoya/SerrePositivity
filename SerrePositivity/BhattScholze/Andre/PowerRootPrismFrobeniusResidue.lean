module

public import SerrePositivity.BhattScholze.Andre.DeltaDivisionFrobeniusResidue
public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialPerfectDelta

/-!
# André E1・E2：実無限根入力の raw 二重剰余と Frobenius

## 概要

完全 prism の無限根 δ 入力上で、prism 生成元の商と選択済みの ϖ の持上げの商を、
Frobenius 側の d 商と p 商へ具体的な環同型で送る。
BS Rem 7.15（著者版 p.62）の完備化前の入力への適用。

## 方針

生成元の distinguished 性を係数 δ 射で移し、逆 Frobenius の係数公式で
無限根環内の逆像を選択済みの係数元と同定する。一般の raw 二重剰余比較を適用する。

## 規約

モニック性や prism 商の p 正則性は、この raw 比較には不要。
prismatic envelope の完備化済みの比較を含まない。

## 使われ方

原典の一元入力や任意の入力族に、補助的な distinguished 性の仮定なしで比較を供給する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "hE" => powerRootPolynomialDelta_isPerfect p W.deltaStructure hW
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)

/-- 概要：無限根入力環内でも選択済みの ϖ の持上げは生成元の逆 Frobenius 像。
方針：係数 Frobenius との可換性と φ(x)=d を使い、Frobenius 同型で消去する。
規約：係数射は既存の標準射。
使われ方：BS Rem 7.15（著者版 p.62）の raw 二重剰余の正確な係数元。 -/
theorem powerRootPrismVarpiLift_inverseFrobenius :
    ((E).frobeniusEquiv hE).symm dP = xP := by
  apply ((E).frobeniusEquiv hE).injective
  rw [RingEquiv.apply_symm_apply]
  change dP = (E).frobeniusLift xP
  rw [powerRootPolynomialDelta_frobenius, powerRootPolynomialFrobenius_coeff,
    perfectPrismVarpiLift_frobenius]

/-- 概要：prism 生成元の係数像は無限根 δ 環でも distinguished。
方針：係数 δ 射による δ 値の可換性と単元の像の単元性を使う。
規約：正則性を追加仮定にしない。
使われ方：BS Rem 7.15（著者版 p.62）の二元イデアル標準化への入力。 -/
theorem powerRootPrismGenerator_isDistinguished : (E).IsDistinguished dP := by
  have hunit := (W.isDistinguished_of_perfect hW).map (algebraMap A P)
  change IsUnit ((algebraMap A P) (W.deltaStructure.delta W.generator)) at hunit
  have hδ := powerRootPolynomialDelta_coeff_isDeltaHom p hW.p_mul_injective
    W.deltaStructure W.generator
  rw [hδ] at hunit
  exact hunit

variable {σ : Type v} (a : σ → PowerRootPolynomial A p (Nat.Prime.pos (Fact.out : p.Prime)))
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "j" => deltaAdjoinDivisionMap E dP a
local notation "Rawφ" => DeltaAdjoinDivision E (DeltaStructure.frobeniusLift E dP)
  (fun s => DeltaStructure.frobeniusLift E (a s))
local notation "jφ" => deltaAdjoinDivisionMap E (DeltaStructure.frobeniusLift E dP)
  (fun s => DeltaStructure.frobeniusLift E (a s))

/-- 概要：無限根入力の raw 二重商は Frobenius 側の d,p 二重商と環同型。
方針：逆 Frobenius 係数元を選択済みの ϖ の持上げへ書き換え、一般比較を適用する。
規約：入力族は任意で、生成元の distinguished 性は完全 prism から供給する。
使われ方：BS Rem 7.15（著者版 p.62）の実入力上の raw 剰余比較。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の係数作用を保つ後続の完備化比較。 -/
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

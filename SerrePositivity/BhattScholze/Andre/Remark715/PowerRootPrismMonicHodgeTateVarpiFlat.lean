module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicHodgeTateBase
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion
public import SerrePositivity.CommutativeAlgebra.AdicFaithfulDescentAlgebra

/-!
# André E1・E2：自然な Hodge–Tate 候補の ϖ 剰余の忠実平坦性

## 概要

無限根モニック実完備化の分母商を T とすると、自然な T/ϖ は R/ϖ 上自由で、正次数なら忠実平坦。
BS Rem 7.15（著者版 p.62）の具体的 pd 剰余からの移送。

## 方針

自然な像イデアル商を既存の二元商へ移し、係数上の可換性を A の代表元で確認する。

## 規約

元の実完備化・基底射を保持し、prism 商の p 正則性はこの剰余平坦性に要求しない。

## 使われ方

分母商の p 正則性と合わせて完全忠実平坦性へ進む。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "xH" => uL (jL xP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "Iv" => Ideal.span {v}
local notation "Rv" => R ⧸ Iv
local notation "S" => H ⧸ Ideal.span {dH, xH}
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f

/-- 概要：自然な基底射による Hodge–Tate 候補の R 代数構造。
方針：検証済みの基底環射から代数構造を得る。
規約：係数作用を移送で選び直さない。
使われ方：BS Rem 7.15（著者版 p.62）の通常剰余テンソル。 -/
@[instance_reducible] def powerRootPrismMonicHodgeTateAlgebra :
    let := pdCompletionCommRing L p (jL dP)
    Algebra R T := by
  let := pdCompletionCommRing L p (jL dP)
  exact (φ).toAlgebra

/-- 概要：自然な像イデアルによる ϖ 商は実完備化の指定二元商と環同型。
方針：像主イデアルを生成元の像で表示し、既存の二重商比較へ移す。
規約：自然な基底射の像イデアルを使う。
使われ方：BS Rem 7.15（著者版 p.62）の自然な剰余係数作用。 -/
def powerRootPrismMonicHodgeTateVarpiMapQuotEquiv :
    let := pdCompletionCommRing L p (jL dP)
    (T ⧸ Ideal.map φ Iv) ≃+* S := by
  let := pdCompletionCommRing L p (jL dP)
  exact (Ideal.quotEquivOfEq (show Ideal.map φ Iv = Ideal.span {φ v} by
    rw [Ideal.map_span, Set.image_singleton])).trans
      (powerRootPrismMonicHodgeTateVarpiEquiv W hW f)

/-- 概要：像イデアル商の比較は実完備化の代表元を保持する。
方針：像主イデアルの書換えと二重商の代表元公式を使う。
規約：全ての実 H⁰ 元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数線形性。 -/
theorem powerRootPrismMonicHodgeTateVarpiMapQuotEquiv_mk (t : H) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateVarpiMapQuotEquiv W hW f
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t)) = Ideal.Quotient.mk _ t := by
  let := pdCompletionCommRing L p (jL dP)
  have h := principalDoubleQuotEquiv_mk dH xH t
  unfold powerRootPrismMonicHodgeTateVarpiMapQuotEquiv
  change principalDoubleQuotEquiv dH xH
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t)) = _
  exact h

/-- 概要：自然な像イデアル商の R/ϖ 代数構造を固定する。
方針：標準商代数構造を元の基底射へ適用する。
規約：同じ像イデアルを型に明示する。
使われ方：BS Rem 7.15（著者版 p.62）の通常剰余の係数作用。 -/
@[instance_reducible] def powerRootPrismMonicHodgeTateVarpiAlgebra :
    let := pdCompletionCommRing L p (jL dP)
    Algebra Rv (T ⧸ Ideal.map φ Iv) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  exact adicQuotientAlgebra Iv T

/-- 概要：比較先の二元商の標準係数作用を同じ環型で固定する。
方針：既存 pd 剰余の係数作用をそのまま用いる。
規約：係数像の公式は既存のものと同一。
使われ方：BS Rem 7.15（著者版 p.62）の商比較の型検査。 -/
@[instance_reducible] def powerRootPrismMonicHodgeTatePDResidueAlgebra (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    Algebra Rv S := by
  let := pdCompletionCommRing L p (jL dP)
  with_reducible exact powerRootPrismMonicVarpiResidueAlgebra W hW f hf

set_option maxHeartbeats 2000000 in
-- 二重商と二元商の巨大な実完備化型について、二つの係数構造の照合に必要。
/-- 概要：自然な ϖ 商と既存 pd 剰余の同型は R/ϖ 線形。
方針：R/ϖ の元を A の代表元へ戻し、両側の自然係数像を照合する。
規約：終域の係数作用は既存の標準係数像と一致する作用を使う。
使われ方：BS Rem 7.15（著者版 p.62）の自由性と忠実平坦性の移送。 -/
def powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    @AlgEquiv Rv (T ⧸ Ideal.map φ Iv) S
      (inferInstance : CommSemiring Rv)
      (inferInstance : Semiring (T ⧸ Ideal.map φ Iv)) (inferInstance : Semiring S)
      (powerRootPrismMonicHodgeTateVarpiAlgebra W hW f)
      (powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  refine { powerRootPrismMonicHodgeTateVarpiMapQuotEquiv W hW f with commutes' := ?_ }
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change powerRootPrismMonicHodgeTateVarpiMapQuotEquiv W hW f
    (Ideal.Quotient.mk _ (φ (Ideal.Quotient.mk W.ideal r))) = _
  rw [powerRootPrismMonicHodgeTateBaseMap_mk,
    powerRootPrismMonicHodgeTateVarpiMapQuotEquiv_mk]
  exact (powerRootPrismMonicVarpiResidueAlgebra_base_coeff W hW f hf r).symm

/-- 概要：自然な Hodge–Tate 候補の ϖ 商は R/ϖ 上自由。
方針：係数を保つ代数同型で既存 pd 剰余の自由性を戻す。
規約：正次数と prism 商の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の通常剰余平坦性。 -/
theorem powerRootPrismMonicHodgeTateVarpi_free (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    Module.Free Rv (T ⧸ Ideal.map φ Iv) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  let := powerRootPrismMonicVarpiResidue_free W hW f hf
  exact Module.Free.of_equiv
    (powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv W hW f hf).symm.toLinearEquiv

/-- 概要：正次数モニック入力の自然な Hodge–Tate 候補の ϖ 商は R/ϖ 上忠実平坦。
方針：係数を保つ代数同型で既存 pd 剰余の忠実平坦性を戻す。
規約：prism 商の p 正則性は不要で、正次数を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の完全忠実平坦性の剰余条件。 -/
theorem powerRootPrismMonicHodgeTateVarpi_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    Module.FaithfullyFlat Rv (T ⧸ Ideal.map φ Iv) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  let := powerRootPrismMonicVarpiResidue_faithfullyFlat W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv Rv S
    (powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv W hW f hf).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

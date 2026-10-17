module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicVarpiPDComparison

/-!
# André E1・E2：実完備化の ϖ 剰余の自然な係数作用と忠実平坦性

## 概要

完全 prism 上の無限根モニック入力について、実完備化を生成元と ϖ 持上げで割った
通常環は R/ϖ 上自由であり、入力が正次数なら忠実平坦。
BS Rem 7.15（著者版 p.62）の具体的 pd 計算による通常平坦性。

## 方針

係数を逆 Frobenius で変更した実 pd 表示から係数作用と自由性を移す。
元の A 係数の完備化像と一致する公式を証明して自然な作用を確認する。

## 規約

実 prismatic 源の同定、元の f の pd 包との同定、源全体の p 正則性は別工程。
原典とは異なる入力の係数変更を明示して用いる。

## 使われ方

実完備化剰余の忠実平坦性を後続の prismatic 源との比較へ供給する。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
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
local notation "S" => H ⧸ Ideal.span {uL (jL dP), uL (jL xP)}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)
local notation "f'" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "zv" => powerRootPolynomialBaseMap Rv p hp (Polynomial.map barr
  (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "F" => powerRootPrismMonicVarpiCompletionPDEquiv W hW f hf

/-- 概要：実完備化の ϖ 剰余に R/ϖ の係数代数構造を与える。
方針：検証済みの主 pd 同型の逆射で標準係数射を戻す。
規約：次の係数公式で元の完備化係数像との一致を確認する。
使われ方：BS Rem 7.15（著者版 p.62）の通常忠実平坦性の自然な係数作用。 -/
@[instance_reducible] def powerRootPrismMonicVarpiResidueAlgebra :
    letI := pdCompletionCommRing L p (jL dP)
    Algebra Rv S := by
  let := pdCompletionCommRing L p (jL dP)
  exact ((F).symm.toRingHom.comp (algebraMap Rv Dv)).toAlgebra

/-- 概要：主 pd 表示への実完備化剰余同型は R/ϖ 代数同型。
方針：逆同型で定めた係数作用に対し順逆合成の公式を使う。
規約：元の実完備化 H⁰ の通常商を維持する。
使われ方：BS Rem 7.15（著者版 p.62）の自由性と忠実平坦性の移送。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の自然な通常係数作用の確認。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の通常平坦性の具体的結論。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の実完備化剰余からの忠実平坦性。 -/
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

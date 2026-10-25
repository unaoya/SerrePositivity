module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicCompletionPairFlat
public import SerrePositivity.BhattScholze.Andre.Remark715.CompletelyFaithfulPairReduction

/-!
# André E1・E2：元の実完備化の二元剰余 H⁰ の忠実平坦性

## 概要

元の実完備化 H の標準 (p,d) 剰余と導来剰余 H⁰ は忠実平坦。
BS Rem 7.15（著者版 p.62）の δ 完全化への入力をそろえる。

## 方針

同じ自然な H/d の p 完全忠実平坦性を二段スカラー拡大と H⁰ 比較で移す。

基礎となる Hodge–Tate 商の完全忠実平坦性は、原典と異なる実源の純性による無条件版を使う。

## 規約

元の係数射を保持し、モニック性・正次数を明示し、prism 商の p 正則性は要求しない。

## 使われ方

完全 δ 基底での Frobenius 段と余極限の剰余忠実平坦性へ渡す。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


include hf hdeg in
/-- 概要：元の実完備化の標準二元剰余は忠実平坦。
方針：自然な主環商作用を照合し、二段剰余の一般判定を適用する。
規約：元の標準係数射で制限した実加群を使う。
使われ方：BS Rem 7.15（著者版 p.62）の導来二元剰余 H⁰。 -/
theorem powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), W.generator})
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {(p : A), W.generator}))).obj
        (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f))) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  let qd := Ideal.Quotient.mk (Ideal.span {W.generator})
  have hred : let := principalAdicQuotientAlgebra W.generator H
      IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ Ideal.span {W.generator})})
        (H ⧸ Ideal.span {algebraMap A H W.generator}) := by
    rw [← powerRootPrismMonicHodgeTateAlgebra_eq_principal W hW f]
    exact powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional
      W hW f hf hdeg
  let := principalAdicQuotientAlgebra W.generator H
  let e := (ModuleCat.extendScalars qd).mapIso
      (powerRootPrismMonicCompletionScalarEquiv W hW f).toModuleIso ≪≫
    (principalScalarExtensionAlgebraQuotientEquiv W.generator H).toModuleIso
  apply pairScalarExtension_faithfullyFlat_of_principal_reduction
  apply isCompletelyFaithfullyFlat_of_linearEquiv _ e.toLinearEquiv.symm
  simpa only [map_natCast] using hred

include hf hdeg in
/-- 概要：元の実完備化の導来二元剰余 H⁰ は忠実平坦。
方針：標準スカラー拡大と実導来底変換 H⁰ の自然な同型で移す。
規約：同じ基底商と標準係数射を使う。
使われ方：BS Rem 7.15（著者版 p.62）の完全 δ 化の剰余判定。 -/
theorem powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), W.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), W.generator})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A), W.generator}))).obj
          (boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)))).obj) := by
  let := pdCompletionCommRing L p (jL dP)
  let q := Ideal.Quotient.mk (Ideal.span {(p : A), W.generator})
  let M := baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)
  let := powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars q).obj M)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

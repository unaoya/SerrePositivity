module

public import SerrePositivity.BhattScholze.Andre.Remark715.CompletelyFlatRegularAlgebraReduction
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicCompletionUniversal
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootHodgeTateReduction
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicCompletionPairFaithful
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-!
# André E1・E2：元の無限根モニック実完備化の二元完全平坦性

## 概要

元の実完備化 H は、元の完全 prism の係数作用について (p,d) 完全平坦。
BS Rem 7.15（著者版 p.62）の δ 完全化に渡す導来剰余の計算。

## 方針

自然な H/d の係数作用と標準主環商の作用を照合し、d の正則性から p 完全平坦性を戻す。

## 規約

元の実 H⁰ と標準係数射を保持する。hpR を仮定せず、モニック性・正次数を要求する。

## 使われ方

元の H の導来 (p,d) 剰余を δ 完全化の一般剰余判定へ渡す。
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
/-- 概要：元の無限根モニック実完備化は (p,d) 完全平坦。
方針：分母正則性と標準作用に移した H/d の p 完全平坦性を一般判定へ渡す。
規約：元の A 係数作用と実 H⁰ を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の完全 δ 化の導来剰余入力。 -/
theorem powerRootPrismMonicCompletion_pair_completelyFlat_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    IsCompletelyFlat (Ideal.span {(p : A), W.generator}) H := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  have hreg : IsSMulRegular H (algebraMap A H W.generator) :=
    powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg
  have hred : let := principalAdicQuotientAlgebra W.generator H
      IsCompletelyFlat (Ideal.span {(p : A ⧸ Ideal.span {W.generator})})
        (H ⧸ Ideal.span {algebraMap A H W.generator}) := by
    rw [← powerRootPrismMonicHodgeTateAlgebra_eq_principal W hW f]
    exact (powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional W hW f hf hdeg).1
  apply completelyFlat_pair_algebra_of_regular_reduction (p : A) W.generator
    W.generator_regular H hreg
  simpa only [map_natCast] using hred

include hf hdeg in
/-- 概要：元の実完備化の (p,d) 標準底変換の高次 Tor は零。
方針：二元完全平坦性を標準剰余係数加群へ適用する。
規約：標準係数作用を持つ加群そのものを使う。
使われ方：BS Rem 7.15（著者版 p.62）の導来剰余の離散性。 -/
theorem powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    scalarExtensionTorVanishing (Ideal.Quotient.mk (Ideal.span {(p : A), W.generator}))
      (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  apply scalarExtensionTorVanishing_of_completelyFlat
  exact isCompletelyFlat_of_linearEquiv _
    (powerRootPrismMonicCompletionScalarEquiv W hW f).symm
    (powerRootPrismMonicCompletion_pair_completelyFlat_of_unconditional W hW f hf hdeg)

include hf hdeg in
/-- 概要：元の実完備化の導来 (p,d) 剰余は非零次数で消える。
方針：高次 Tor の消滅から標準増大同型を作り、単項複体のホモロジーを使う。
規約：標準係数射で制限した実加群の導来底変換を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の δ 完全化の剰余計算。 -/
theorem powerRootPrismMonicCompletion_pair_reduction_homology_isZero_of_unconditional
    (i : ℤ) (hi : i ≠ 0) :
    let := pdCompletionCommRing L p (jL dP)
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), W.generator})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
        (Ideal.span {(p : A), W.generator}))).obj
        (boundedAboveDerivedSingleFunctor.obj
          (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)))).obj) := by
  let := pdCompletionCommRing L p (jL dP)
  let q := Ideal.Quotient.mk (Ideal.span {(p : A), W.generator})
  let M := baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)
  let e := boundedAboveDerivedBaseChangeModuleAugmentationIso q M
    (powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing_of_unconditional W hW f hf hdeg)
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q).obj M) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat _) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e))

include hf hdeg in
/-- 概要：元の実完備化の標準二元剰余は忠実平坦。
方針：自然な主環商作用を照合し、二段剰余の一般判定を適用する。
規約：元の標準係数射で制限した実加群を使う。
使われ方：BS Rem 7.15（著者版 p.62）の導来二元剰余 H⁰。 -/
theorem powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat_of_unconditional :
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
    exact powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional W hW f hf hdeg
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
theorem powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat_of_unconditional :
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
  let := powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat_of_unconditional W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars q).obj M)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

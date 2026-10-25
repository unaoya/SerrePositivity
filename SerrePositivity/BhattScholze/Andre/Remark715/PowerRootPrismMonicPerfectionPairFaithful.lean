module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicCompletionPairFaithful
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaAlgebra.PerfectPrismDeltaAlgebraPDCompletelyFlat

/-!
# André E1・E2：元の実完備化を完全 δ 化した後の二元剰余

## 概要

元の無限根モニック実完備化を完全 δ 化し再完備化しても、標準二元導来剰余は離散で H⁰ は忠実平坦。
BS Rem 7.15（著者版 p.62）の完全化後への平坦性の保存。

## 方針

完全 δ 基底での一般 Frobenius 段・余極限・実完備化の剰余判定に具体的入力を渡す。

基礎となる Hodge–Tate 商の完全忠実平坦性は、原典と異なる実源の純性による無条件版を使う。

## 規約

元の係数射・δ 構造を保持し、モニック性・正次数を明示し、prism 商の p 正則性は要求しない。

## 使われ方

最終 perfectoid 商の p 完全忠実平坦性を証明するための prism 側の入力。
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


local notation "c" => powerRootPrismMonicCompletionBaseMap W hW f
local notation "κ" => deltaAlgebraPerfectionCoefficient DH c
local notation "Cp" => DeltaPerfection DH
local notation "Hp" => PDCompletionH0 Cp p (κ W.generator)
local notation "t" => RingHom.comp (pdCompletionUnit Cp p (κ W.generator)) κ
local notation "M" => baseChangeScalarModule t
local notation "I" => Ideal.span {(p : A), W.generator}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M)
include hf hdeg

/-- 概要：完全 δ 化後の同じ実完備化の導来二元剰余の非零次数は消える。
方針：元の実完備化の導来剰余計算を一般の完全化剰余判定へ渡す。
規約：同じ標準係数射と明示仮定を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の最終商の完全忠実平坦性。 -/
theorem powerRootPrismMonicCompletedPerfection_pair_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p (κ W.generator)
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p (κ W.generator)
  exact perfectPrismDeltaAlgebraPD_reduction_homology_isZero W DH c hW
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
    (powerRootPrismMonicCompletion_pair_reduction_homology_isZero W hW f hf hdeg)
    (powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat W hW f hf hdeg) i hi

/-- 概要：完全 δ 化後の同じ実完備化の導来二元剰余 H⁰ は忠実平坦。
方針：元の実完備化の導来剰余計算を一般の完全化剰余判定へ渡す。
規約：同じ標準係数射と明示仮定を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の最終商の完全忠実平坦性。 -/
theorem powerRootPrismMonicCompletedPerfection_pairH0_faithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p (κ W.generator)
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p (κ W.generator)
  exact perfectPrismDeltaAlgebraPD_reductionH0_faithfullyFlat W DH c hW
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
    (powerRootPrismMonicCompletion_pair_reduction_homology_isZero W hW f hf hdeg)
    (powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat W hW f hf hdeg)

/-- 概要：完全 δ 化後の同じ実完備化の標準係数加群は二元完全忠実平坦。
方針：元の実完備化の導来剰余計算を一般の完全化剰余判定へ渡す。
規約：同じ標準係数射と明示仮定を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の最終商の完全忠実平坦性。 -/
theorem powerRootPrismMonicCompletedPerfection_pair_completelyFaithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p (κ W.generator)
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p (κ W.generator)
  exact perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat W DH c hW
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
    (powerRootPrismMonicCompletion_pair_reduction_homology_isZero W hW f hf hdeg)
    (powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat W hW f hf hdeg)

end SerrePositivity.BhattScholze.Andre

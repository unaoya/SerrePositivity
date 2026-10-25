module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicPerfectionPairFaithful
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicCompletedPerfection
public import SerrePositivity.BhattScholze.Andre.Variants.PerfectedDeltaAlgebraQuotientFaithful

/-!
# André E1・E2：元の無限根候補の完全化後商の p 完全忠実平坦性

## 概要

完全 δ 化・再完備化後の生成元商は、元の自然な基底射について p 完全忠実平坦。
BS Rem 7.15（著者版 p.62）の一元根付き候補の平坦性。

## 方針

完全化後の分母正則性を完全 δ prism で確認し、正則主商の一般下降判定を使う。

基礎となる Hodge–Tate 商の完全忠実平坦性は、原典と異なる実源の純性による無条件版を使う。

## 規約

元の係数射と具体的候補を保持し、モニック性・正次数を明示し、prism 商の p 正則性は要求しない。
原典とは異なる Tor 底変換と完全 δ 化後の剰余判定の経路である。

## 使われ方

同じ最終 perfectoid 候補の整 perfectoid 性・根方程式と結び付ける。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
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
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


local notation "c" => powerRootPrismMonicCompletionBaseMap W hW f
local notation "κ" => deltaAlgebraPerfectionCoefficient DH c
local notation "Cp" => DeltaPerfection DH
local notation "x" => deltaPerfectionOf DH 0 (uL (jL dP))
local notation "Hp" => PDCompletionH0 Cp p x
local notation "t" => RingHom.comp (pdCompletionUnit Cp p x) κ
local notation "M" => baseChangeScalarModule t
local notation "I" => Ideal.span {(p : A), W.generator}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M)
local notation "sC" => pdCompletionUnit Cp p x
local notation "T∞" => PDCompletionH0 Cp p x ⧸ Ideal.span {sC x}

/-- 概要：完全化後の実完備化の元の A 係数作用。
方針：標準完全化係数射から代数構造を取る。
規約：作用自体にモニック性・正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の正則主商への下降。 -/
@[instance_reducible] def powerRootPrismMonicPerfectionAlgebra :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p x
    Algebra A Hp := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p x
  exact (t).toAlgebra

/-- 概要：完全化後の実完備化では指定分母が正則。
方針：完全 δ 環の distinguished 元の実完備化の prism 性を使う。
規約：分母は元の標準係数射による像。
使われ方：BS Rem 7.15（著者版 p.62）の生成元商の導来比較。 -/
theorem powerRootPrismMonicPerfection_generator_regular :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p x
    IsSMulRegular Hp (t W.generator) := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing Cp p x
  have hk := deltaAlgebraPerfectionCoefficient_isDeltaHom W.deltaStructure DH c
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
  have hd := hk.map_isDistinguished (W.isDistinguished_of_perfect hW)
  exact (perfectDeltaPDPrism (deltaPerfectionStructure DH) (deltaPerfection_isPerfect DH)
    x hd).generator_regular

include hf hdeg in
/-- 概要：同じ完全化後 perfectoid 商の自然な基底射は p 完全忠実平坦。
方針：一般の δ 代数商判定に実剰余入力を渡し、標準係数射を代表元上で照合する。
規約：モニック性・正次数を仮定し、prism 商の p 正則性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の具体的根付き perfectoid 候補。 -/
theorem powerRootPrismMonicCompletedPerfectionBaseMap_completelyFaithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing Cp p x
    let := (powerRootPrismMonicCompletedPerfectionBaseMap W hW f).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ W.ideal)}) T∞ := by
  let := pdCompletionCommRing L p (jL dP)
  let G := DH
  let Cq := DeltaPerfection G
  let i := deltaPerfectionOf G 0
  let b := i (uL (jL dP))
  let := pdCompletionCommRing Cq p b
  have hb : deltaAlgebraPerfectionCoefficient G c W.generator = b := rfl
  let g := perfectedDeltaAlgebraQuotientBaseMap W G c b hb
  have hg : g = powerRootPrismMonicCompletedPerfectionBaseMap W hW f := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    rfl
  have h := perfectedDeltaAlgebraQuotientBaseMap_completelyFaithfullyFlat W G c hW
    (powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f)
    (powerRootPrismMonicCompletion_pair_reduction_homology_isZero W hW f hf hdeg)
    (powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat W hW f hf hdeg) b hb
  let F (qmap : (A ⧸ W.ideal) →+* T∞) :=
    let := qmap.toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ W.ideal)}) T∞
  have hF : F g := h
  exact Eq.mp (congrArg F hg) hF

end SerrePositivity.BhattScholze.Andre

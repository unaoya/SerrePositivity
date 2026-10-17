module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicEnvelopeInitial
public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootCompletionPairFlat

/-!
# André A1-a：正次数モニック入力に対する元の源 prism の初期性

## 概要

元の H の prism 性と原典の完備入力作用を持つ有界 prism 圏での初期性を証明する。
BS Rem 7.15（著者版 p.62）の源の構成と普遍性の合流。

## 方針

A1-b の元の H の生成元正則性と同じ T の有界性を、既存の条件付き初期性へ渡す。
原典を補う実逐次完備化・純性・明示的な入力圏による経路。

## 規約

完全 prism と正次数モニック入力だけを仮定し、hpR・hreg・hBound は引数に残さない。
固定完全基底と向き付き prism の圏での初期性を扱う。絶対 site 全体との比較は別工程。

## 使われ方

原典の完備入力環 S の作用を持つ元の源と、同じ圏の任意の envelope の比較に使う。
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
variable (f : Polynomial A)
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


local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "PR" => PowerRootPolynomial R p hp
local notation "CR" => AdicCompletion (Ideal.span {(p : PR)}) PR
local notation "zR" => powerRootPolynomialBaseMap R p hp fR
local notation "SI" => PowerRootMonicCompletedInput p hp fR
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})) (algebraMap PR CR)
local notation "S₀" => PowerRootEquationQuotient p hp fR
local notation "CS" => AdicCompletion (Ideal.span {(p : S₀)}) S₀
local notation "jS" => algebraMap S₀ CS
local notation "qR" => Ideal.Quotient.mk (Ideal.span {zR})

open CategoryTheory CategoryTheory.Limits
local notation "cS" => RingHom.comp lS (algebraMap R PR)
variable (hf : f.Monic)

variable (hdeg : 0 < f.natDegree)

set_option maxHeartbeats 800000 in
-- 元の H の環構造と A1-b の生成元正則性の依存型を照合するため。
/-- 概要：正次数モニック入力から元の H に prism 構造を与える。
方針：A1-b の同じ標準分母像の正則性を既存の prism 構成へ渡す。
規約：prism 商の p 正則性や源の正則性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の prismatic 源。 -/
def powerRootPrismMonicCompletionPrismOfMonicPositive :
    let := pdCompletionCommRing L p (jL dP)
    OrientedPrism p H := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicCompletionPrismOfRegular W hW f
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)

set_option maxHeartbeats 800000 in
-- 元の H の prism 構造の生成元を定義と照合するため。
/-- 概要：正次数モニック源 prism の生成元は元の標準分母像。
方針：正則性から作った prism の計算規則を使う。
規約：同じ H と同じ生成元を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の元の H/dH の同定。 -/
theorem powerRootPrismMonicCompletionPrismOfMonicPositive_generator :
    let := pdCompletionCommRing L p (jL dP)
    (powerRootPrismMonicCompletionPrismOfMonicPositive W hW f hf hdeg).generator =
      uL (jL dP) := by
  rfl

set_option maxHeartbeats 800000 in
-- 完備入力の係数作用と元の H の正則性・有界性を一つの対象で照合するため。
/-- 概要：正次数モニック入力から元の H を有界入力 prism の対象とする。
方針：A1-b の生成元正則性と同じ通常商 T の有界性を既存の構成へ渡す。
規約：hpR・hreg・hBound を引数に残さず、原典の順序の完備入力環を使う。
使われ方：BS Rem 7.15（著者版 p.62）の標準源の初期性。 -/
def powerRootPrismMonicSourceInputObjectOfMonicPositive : BoundedPrismInput W cS := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicSourceInputObject W hW f hf
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg)

set_option maxHeartbeats 800000 in
-- 元の H の依存する入力対象と既存の初期性の型を照合するため。
/-- 概要：元の正次数モニック源は有界入力 prism の圏で初期。
方針：A1-b の同じ H と T の結果により初期性の二つの補助仮定を解消する。
規約：固定完全基底・向き付き対象の圏での結果であり、絶対 site 比較は別工程。
使われ方：BS Rem 7.15（著者版 p.62）の envelope 比較の合流点。 -/
def powerRootPrismMonicSourceInput_isInitialOfMonicPositive :
    IsInitial (powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg) := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicSourceInput_isInitial W hW f hf
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg)

set_option maxHeartbeats 800000 in
-- 同じ H の台環と入力圏の任意の初期対象との比較を保つため。
/-- 概要：同じ入力圏の任意の初期対象と元の正次数モニック源 H は環同型。
方針：補助仮定を A1-b から供給して既存の初期対象比較を適用する。
規約：比較先の初期性だけはその普遍性として明示する。
使われ方：BS Rem 7.15（著者版 p.62）の同じ圏での envelope の一意性。 -/
def powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive
    (Z : BoundedPrismInput W cS) (hZ : IsInitial Z) :
    let := pdCompletionCommRing L p (jL dP)
    H ≃+* Z.ring := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicSourceEnvelopeRingEquiv W hW f hf
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg) Z hZ

set_option maxHeartbeats 800000 in
-- 同型の基底保存性を元の H の全係数像の公式として照合するため。
/-- 概要：正次数モニック源と任意の初期対象の環同型は元の A の係数像を保つ。
方針：既存の基底保存公式に A1-b の正則性・有界性を代入する。
規約：元の標準係数射を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の原典との係数作用の比較。 -/
theorem powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_base_coeff
    (Z : BoundedPrismInput W cS) (hZ : IsInitial Z) (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive W hW f hf hdeg Z hZ
      (powerRootPrismMonicCompletionBaseMap W hW f a₀) = Z.base.toRingHom a₀ := by
  let := pdCompletionCommRing L p (jL dP)
  exact powerRootPrismMonicSourceEnvelopeRingEquiv_base_coeff W hW f hf a₀
    (powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg) Z hZ

end SerrePositivity.BhattScholze.Andre

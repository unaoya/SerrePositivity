module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicFullFrobeniusPD
public import SerrePositivity.BhattScholze.Andre.Unconditional.MonicPDEnvelope

/-!
# André E1・E2：追加正則性なしの実 Frobenius 引戻しの pd 普遍性

## 概要

A 全体の自然な実 Frobenius 引戻しは、モニック性のみの下で元の mod p 入力の実 pd 包となる。
BS Rem 7.15(1)（著者版 p.62）の φ_A 引戻しの pd 比較から prism 商の p 正則性を除く。

## 方針

射影的な正次数商を使って構成した比較先の実分冪構造を、検証済みの自然な入力環同型で戻す。
原典とは異なる線形切断・半線形比較・通常テンソル・実分冪構造の移送による証明。

## 規約

完全 prism とモニック性のみを要求する。原典の係数表記との最終照合と絶対 prismatic 源の同定は別工程。

## 使われ方

実 Frobenius 引戻しそのものから、追加正則性なしに任意の分冪標的への一意な射を得る。
-/

@[expose] public noncomputable section
universe u w
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
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

local notation "Rp" => R ⧸ Ideal.span {(p : R)}
local notation "Np" => PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dp" => PrincipalDPPresentation Np zp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "Mv" => T ⧸ Ideal.map φ Iv

local notation "bv" => RingHom.comp (Ideal.Quotient.mk Iv) (Ideal.Quotient.mk W.ideal)
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "Ac" => TensorBaseCopy A
local notation "downA" => RingEquiv.toRingHom (tensorBaseCopyRingEquiv A)
local notation "αc" => RingEquiv.trans frob (RingEquiv.symm (tensorBaseCopyRingEquiv A))
local notation "rA" => RingHom.comp (algebraMap Rp Dp) bp
local notation "U" => powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f

local notation "qA" => powerRootPrismMonicVarpiBaseMap W hW f
local notation "At" => Ac ⊗[A] Mv
local notation "Ef" => powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f

variable (hf : f.Monic)
local notation "Ein" => powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf

/-- 概要：自然な A 全体の実引戻し上に元の mod p 入力の実分冪構造を与える。
方針：係数を保つ実同型に沿って比較先の構造を戻す。
規約：prism 商の p 正則性・正次数を仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の構造。 -/
def powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    DividedPowers (powerRootPrismMonicFullFrobeniusPDIdeal W hW f hf) := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceDividedPowers zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)

/-- 概要：A 全体の実引戻し比較は元の実分冪構造を比較先へ保つ。
方針：同型の源へ戻した構造の分冪射性を使う。
規約：同じ入力環作用と同じイデアルを使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 比較。 -/
theorem powerRootPrismMonicFullFrobeniusInputAlgEquiv_isDPMorphism_of_unconditional :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    (powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional W hW f hf).IsDPMorphism
      (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf) (Ein).toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceEquiv_isDPMorphism zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)

/-- 概要：自然な入力元の全分冪は標準分冪生成元の実同型による逆像。
方針：比較先の標準分冪値を係数を保つ同型で戻す。
規約：零次数を含む全次数 n を指定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪値の同定。 -/
theorem powerRootPrismMonicFullFrobeniusDividedPowers_input_apply_of_unconditional
    (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    (powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional W hW f hf).dpow n
      (algebraMap Np At zp) = (Ein).symm (principalDPGenerator zp n) := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceDividedPowers_base_apply zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)
    (powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional W hW f hf) n

/-- 概要：自然な実 Frobenius テンソルは元の mod p 入力の pd 包の普遍性を持つ。
方針：同じ入力環上の代数同型で標準主分冪包の普遍性を移す。
原典とは異なる半線形比較・通常テンソル・実分冪構造の移送による証明。
規約：標的の宇宙・ねじれ・完備性は制約しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実引戻し側の pd 包性。 -/
theorem existsUnique_powerRootPrismMonicFullFrobeniusPDMorphism_of_unconditional
    {B : Type w} [CommRing B] [Algebra Np B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    ∃! F : At →ₐ[Np] B,
      (powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional W hW f hf).IsDPMorphism
        Ht F.toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact existsUnique_principalPDSourceMorphism zp Ein
    (powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf)
    (powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional W hW f hf) Ht hzB

end SerrePositivity.BhattScholze.Andre

module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicFullFrobeniusPullback

/-!
# André R1：A 全体の Frobenius 引戻しの PD 入力とイデアル

## 概要

A 全体の Frobenius 引戻しにおける標準入力環作用、比較同型、分冪イデアルを保持する。
BS Rem 7.15(1)（著者版 p.62）の元の入力と同じ台環を使う。

## 方針

係数と根変数を保つ比較同型により入力作用と指定イデアルを作る。
原典とは異なる半線形比較・通常テンソルを使う経路。

## 規約

不要になった hpR 付きの分冪構造・分冪射・分冪公式・普遍性の4宣言を削除した。
対応する `_of_unconditional` 版を集約から公開し、モニック性を保持して正次数は追加しない。

## 使われ方

無条件の分冪構造を、同じ元の実引戻しと同じ入力作用に関して適用する。
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

/-- 概要：A 全体の実引戻しに元の mod p 無限根環の代数作用を与える。
方針：A 全体の実引戻し同型の逆で標準入力係数射を戻す。
規約：次の係数・根変数公式で自然性を確認する。
使われ方：BS Rem 7.15（著者版 p.62）の実 pd 源の係数作用。 -/
@[instance_reducible] def powerRootPrismMonicFullFrobeniusInputAlgebra (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    Algebra Np At := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  exact ((Ef hf).symm.toRingHom.comp (algebraMap Np Dp)).toAlgebra

/-- 概要：A 全体の実引戻し比較は同じ無限根環上の代数同型。
方針：逆同型で戻した作用と順逆の合成を照合する。
規約：元の左 A 代数同型と同じ環同型を使う。
使われ方：BS Rem 7.15（著者版 p.62）の分冪包の普遍性の移送。 -/
def powerRootPrismMonicFullFrobeniusInputAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    At ≃ₐ[Np] Dp := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  refine { (Ef hf).toRingEquiv with commutes' := ?_ }
  intro r
  exact (Ef hf).apply_symm_apply (algebraMap Np Dp r)

/-- 概要：入力環作用の元の A 係数像は左 A の標準係数像と一致する。
方針：比較の単射性・入力係数の可換性・左 A 線形性を使う。
規約：A の全係数元について二つの作用の一致を述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の元の多項式の係数を保持する。 -/
theorem powerRootPrismMonicFullFrobeniusInputAlgebra_base_coeff
    (hf : f.Monic) (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    algebraMap Np At (algebraMap Rp Np (bp a₀)) =
      algebraMap Ac At (⟨a₀⟩ : Ac) := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  let q := powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf
  apply q.injective
  calc
    q (algebraMap Np At (algebraMap Rp Np (bp a₀))) =
        algebraMap Np Dp (algebraMap Rp Np (bp a₀)) := q.commutes _
    _ = algebraMap Rp Dp (bp a₀) := (IsScalarTower.algebraMap_apply Rp Np Dp (bp a₀)).symm
    _ = q (algebraMap Ac At (⟨a₀⟩ : Ac)) := ((Ef hf).commutes (⟨a₀⟩ : Ac)).symm

/-- 概要：第 n 入力根変数は元の第 n+1 根変数の標準像とのテンソル。
方針：入力環同型の単射性と A 全体の引戻しの根変数公式を使う。
規約：選び直した根ではなく元の入力射の像を使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の自然な無限根入力環作用。 -/
theorem powerRootPrismMonicFullFrobeniusInputAlgebra_variable
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (powerRootPolynomialVariable A p hp (n + 1))
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    algebraMap Np At (powerRootPolynomialVariable Rp p hp n) = (1 : Ac) ⊗ₜ[A] m := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (powerRootPolynomialVariable A p hp (n + 1))
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  let q := powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf
  apply q.injective
  calc
    q (algebraMap Np At (powerRootPolynomialVariable Rp p hp n)) =
        algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n) := q.commutes _
    _ = q ((1 : Ac) ⊗ₜ[A] m) :=
      (powerRootPrismMonicFullFrobeniusPullbackAlgEquiv_variable W hW f hf n).symm

variable (hf : f.Monic)
local notation "Ein" => powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf

/-- 概要：A 全体の実引戻しの分冪イデアルは標準正次数イデアルの逆像。
方針：自然な入力環上の代数同型の逆で像イデアルを取る。
規約：元の A 全体の実引戻し環を維持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪構造の台イデアル。 -/
def powerRootPrismMonicFullFrobeniusPDIdeal :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    Ideal At := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceIdeal zp Ein

/-- 概要：自然な A 全体の実引戻しの分冪イデアルは元の入力の像を含む。
方針：係数を保つ同型の源への入力所属の一般公式を使う。
規約：モニック性のみを仮定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の分冪包の入力条件。 -/
theorem powerRootPrismMonicFullFrobeniusPDIdeal_input_mem :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    algebraMap Np At zp ∈ powerRootPrismMonicFullFrobeniusPDIdeal W hW f hf := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceIdeal_base_mem zp Ein

end SerrePositivity.BhattScholze.Andre

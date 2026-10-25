module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicFrobeniusRootAction
public import SerrePositivity.BhattScholze.Andre.Variants.PrincipalPDSourceTransport

/-!
# André E1・E2：実 Frobenius テンソル上の無限根環の自然な代数作用

## 概要

実テンソルの無限根環作用は、元の次段の根変数の像と自然な係数作用で記述できる。
BS Rem 7.15（著者版 p.62）の pd 包の入力環との比較。

## 方針

検証済みのテンソル同型で作用を戻し、全ての係数と全ての根変数上で自然な像を証明する。

## 規約

作用を暗黙の移送として残さず、係数・根変数の像を公開する。モニック性のみを仮定する。

## 使われ方

同じ実テンソルを無限根環上の実 pd 包として扱う。
-/

@[expose] public noncomputable section
universe u
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

local notation "Ft" => Rp ⊗[Rv] Mv
local notation "Et" => powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv W hW f

/-- 概要：実テンソルに元の mod p 無限根環の代数作用を与える。
方針：実テンソル同型の逆で標準入力係数射を戻す。
規約：次の係数・根変数公式で自然性を確認する。
使われ方：BS Rem 7.15（著者版 p.62）の実 pd 源の係数作用。 -/
@[instance_reducible] def powerRootPrismMonicFrobeniusTensorInputAlgebra (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    Algebra Np Ft := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  exact ((Et hf).symm.toRingHom.comp (algebraMap Np Dp)).toAlgebra

/-- 概要：実テンソル比較は同じ無限根環上の代数同型。
方針：逆同型で戻した作用と順逆の合成を照合する。
規約：元の Rp 代数同型と同じ環同型を使う。
使われ方：BS Rem 7.15（著者版 p.62）の分冪包の普遍性の移送。 -/
def powerRootPrismMonicFrobeniusTensorInputAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    Ft ≃ₐ[Np] Dp := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  refine { (Et hf).toRingEquiv with commutes' := ?_ }
  intro r
  exact (Et hf).apply_symm_apply (algebraMap Np Dp r)

/-- 概要：実テンソルの入力環作用は元の Rp 係数作用と一致する。
方針：実テンソル同型の単射性と係数作用の塔を使う。
規約：Rp の任意の元を含む。
使われ方：BS Rem 7.15（著者版 p.62）の自然な底環作用。 -/
theorem powerRootPrismMonicFrobeniusTensorInputAlgebra_coeff
    (hf : f.Monic) (r : Rp) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    algebraMap Np Ft (algebraMap Rp Np r) = algebraMap Rp Ft r := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  let q := powerRootPrismMonicFrobeniusTensorInputAlgEquiv W hW f hf
  apply q.injective
  calc
    q (algebraMap Np Ft (algebraMap Rp Np r)) =
        algebraMap Np Dp (algebraMap Rp Np r) := q.commutes _
    _ = algebraMap Rp Dp r := (IsScalarTower.algebraMap_apply Rp Np Dp r).symm
    _ = q (algebraMap Rp Ft r) := ((Et hf).commutes r).symm

/-- 概要：第 n 入力根変数は元の第 n+1 根変数の標準像とのテンソル。
方針：実比較の単射性と検証済みの根変数公式を使う。
規約：全段 n で同じ自然な根の族を使う。
使われ方：BS Rem 7.15（著者版 p.62）の入力環作用の自然性。 -/
theorem powerRootPrismMonicFrobeniusTensorInputAlgebra_variable
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (powerRootPolynomialVariable A p hp (n + 1))
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    algebraMap Np Ft (powerRootPolynomialVariable Rp p hp n) = (1 : Rp) ⊗ₜ[Rv] m := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (powerRootPolynomialVariable A p hp (n + 1))
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  let q := powerRootPrismMonicFrobeniusTensorInputAlgEquiv W hW f hf
  apply q.injective
  calc
    q (algebraMap Np Ft (powerRootPolynomialVariable Rp p hp n)) =
        algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n) := q.commutes _
    _ = q ((1 : Rp) ⊗ₜ[Rv] m) :=
      (powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_variable W hW f hf n).symm

/-- 概要：通常多項式の入力像は元の第一根変数のテンソルで評価した値。
方針：評価と環射の可換性に、自然な係数作用と第零入力変数の公式を使う。
規約：任意の Rp 係数多項式を含む。
使われ方：BS Rem 7.15（著者版 p.62）の元の f の入力を実テンソルで明示する。 -/
theorem powerRootPrismMonicFrobeniusTensorInputAlgebra_polynomial
    (hf : f.Monic) (g : Polynomial Rp) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (powerRootPolynomialVariable A p hp 1)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    algebraMap Np Ft (powerRootPolynomialBaseMap Rp p hp g) =
      g.eval₂ (algebraMap Rp Ft) ((1 : Rp) ⊗ₜ[Rv] m) := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (powerRootPolynomialVariable A p hp 1)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  let q := powerRootPrismMonicFrobeniusTensorInputAlgEquiv W hW f hf
  change algebraMap Np Ft
    (g.eval₂ (algebraMap Rp Np) (powerRootPolynomialVariable Rp p hp 0)) = _
  exact principalPDSourcePolynomialEvaluation zp q
    (powerRootPolynomialVariable Rp p hp 0) ((1 : Rp) ⊗ₜ[Rv] m)
    (fun r => (Et hf).commutes r)
    (fun r => (IsScalarTower.algebraMap_apply Rp Np Dp r).symm)
    (powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_variable W hW f hf 0) g

/-- 概要：元の Rp 係数作用・無限根作用・実テンソル作用は作用の塔をなす。
方針：全係数での代数射の一致を使う。
規約：元の二つの作用を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の係数作用の整合性。 -/
theorem powerRootPrismMonicFrobeniusTensorInputScalarTower (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    IsScalarTower Rp Np Ft := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  exact (powerRootPrismMonicFrobeniusTensorInputAlgebra_coeff W hW f hf r).symm

end SerrePositivity.BhattScholze.Andre

module

public import SerrePositivity.BhattScholze.Andre.AutomorphismTensorPullback
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicFrobeniusTensorPD

/-!
# André E1・E2：A 全体の Frobenius 引戻しと実 pd 表示

## 概要

自然な実 Hodge–Tate ϖ 商を A 全体の Frobenius に沿って引き戻すと、
元の f の mod p 入力の主分冪表示と左 A 代数同型になる。
BS Rem 7.15(1)（著者版 p.62）の φ_A 引戻しの通常テンソルによる比較。

## 方針

自然な A 係数射を確認し、剰余比較の係数公式を A の半線形性へ持ち上げる。
原典とは異なる半線形環同型と実テンソルの普遍性による経路。

## 規約

左の A を同じ宇宙の TensorBaseCopy A で区別し、左への A 作用を Frobenius とする。
比較先の係数環は R/p と明示し、絶対 prismatic 源の同定は別工程。

## 使われ方

商環間の係数テンソルだけでなく、A 上の Frobenius 引戻しの根変数と pd 構造を扱う。
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

local notation "bv" => RingHom.comp (Ideal.Quotient.mk Iv) (Ideal.Quotient.mk W.ideal)
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "Ac" => TensorBaseCopy A
local notation "downA" => RingEquiv.toRingHom (tensorBaseCopyRingEquiv A)
local notation "αc" => RingEquiv.trans frob (RingEquiv.symm (tensorBaseCopyRingEquiv A))
local notation "rA" => RingHom.comp (algebraMap Rp Dp) bp
local notation "U" => powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f

/-- 概要：実 ϖ 商の A 係数射は元の自然な R/ϖ 作用の合成。
方針：二段商係数射と既存の自然な商代数作用を合成する。
規約：Frobenius でねじる前の元の係数作用を固定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の A 上の実引戻しの右因子。 -/
def powerRootPrismMonicVarpiBaseMap :
    let := pdCompletionCommRing L p (jL dP)
    A →+* Mv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  exact (algebraMap Rv Mv).comp bv

/-- 概要：実 ϖ 商の A 係数射は元の無限根入力射の係数制限と一致する。
方針：自然な基底射の代表元公式と商代数の定義を使う。
規約：元の完備化単位と商射を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の元の A 作用の照合。 -/
theorem powerRootPrismMonicVarpiBaseMap_coeff (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicVarpiBaseMap W hW f a₀ =
      powerRootPrismMonicVarpiInputMap W hW f (algebraMap A P a₀) := by
  let := pdCompletionCommRing L p (jL dP)
  exact congrArg (Ideal.Quotient.mk (Ideal.map φ Iv))
    (powerRootPrismMonicHodgeTateBaseMap_mk W hW f a₀)

/-- 概要：実剰余の半線形比較は A 係数に A 自身の Frobenius を作用させる。
方針：R/ϖ 係数公式と係数商同型の代表元公式を合成する。
規約：モニック性以外の次数・p 正則性仮定は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の A 全体の引戻しに必要な半線形性。 -/
theorem powerRootPrismMonicVarpiFrobeniusResidueEquiv_base_coeff
    (hf : f.Monic) (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    U hf (powerRootPrismMonicVarpiBaseMap W hW f a₀) = rA ((frob) a₀) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  change U hf (algebraMap Rv Mv (bv a₀)) = _
  rw [powerRootPrismMonicVarpiFrobeniusResidueEquiv_coeff]
  exact congrArg (algebraMap Rp Dp)
    (perfectPrismVarpiFrobeniusQuotientEquiv_mk W hW a₀)

local notation "qA" => powerRootPrismMonicVarpiBaseMap W hW f
local notation "At" => Ac ⊗[A] Mv

/-- 概要：A 上の実 Frobenius 引戻しは元の mod p 入力の主分冪表示と左 A 線形同型。
方針：A 係数の半線形性に自己同型に沿うテンソル比較を適用する。
規約：左 A は型の写し、右因子は自然な実 ϖ 商で、A 作用は明示したものを使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の φ_A 引戻し全体の実比較。 -/
def powerRootPrismMonicFullFrobeniusPullbackAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    At ≃ₐ[Ac] Dp := by
  let := pdCompletionCommRing L p (jL dP)
  exact automorphismTensorPullbackAlgEquiv frob qA rA (U hf)
    (powerRootPrismMonicVarpiFrobeniusResidueEquiv_base_coeff W hW f hf)

/-- 概要：A 全体の引戻し比較の単純テンソル公式。
方針：自己同型テンソル比較の公式を実剰余へ適用する。
規約：左の係数は元の A の元で指定し、全ての実 ϖ 商元を含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の標準係数と自然な根変数の追跡。 -/
theorem powerRootPrismMonicFullFrobeniusPullbackAlgEquiv_tmul (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    ∀ (a₀ : A) (m : Mv),
      powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f hf
        ((⟨a₀⟩ : Ac) ⊗ₜ[A] m) = algebraMap Rp Dp (bp a₀) * U hf m := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  dsimp only
  intro a₀ m
  exact automorphismTensorPullbackAlgEquiv_tmul frob qA rA (U hf)
    (powerRootPrismMonicVarpiFrobeniusResidueEquiv_base_coeff W hW f hf) a₀ m

/-- 概要：A 全体の引戻し比較は元の第 n+1 根変数を第 n 根変数へ送る。
方針：単純テンソル公式で係数 1 を消し、実剰余比較の根変数公式を使う。
規約：元の自然な入力射と全ての段 n を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の入力環作用を A 引戻し上で照合する。 -/
theorem powerRootPrismMonicFullFrobeniusPullbackAlgEquiv_variable
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (powerRootPolynomialVariable A p hp (n + 1))
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f hf
      ((1 : Ac) ⊗ₜ[A] m) = algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n) := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (powerRootPolynomialVariable A p hp (n + 1))
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  have hunit : algebraMap Rp Dp (bp (1 : A)) = 1 :=
    (congrArg (algebraMap Rp Dp) (map_one bp)).trans (map_one (algebraMap Rp Dp))
  calc
    powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f hf
        ((1 : Ac) ⊗ₜ[A] m) = algebraMap Rp Dp (bp (1 : A)) * U hf m :=
      powerRootPrismMonicFullFrobeniusPullbackAlgEquiv_tmul W hW f hf 1 m
    _ = U hf m :=
      (congrArg (fun z : Dp => z * U hf m) hunit).trans (one_mul (U hf m))
    _ = algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n) :=
      powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable_succ W hW f hf n

end SerrePositivity.BhattScholze.Andre

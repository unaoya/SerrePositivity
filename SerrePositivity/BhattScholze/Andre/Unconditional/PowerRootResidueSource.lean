module

public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootResidueKoszul
public import SerrePositivity.BhattScholze.DeltaDivisionSourceResidueTensor
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-!
# 元の無限根モニック残余源の無条件の導来評価比較

## 概要
BS Rem 7.15（著者版 p.62）の元の実残余自由 δ 源の導来評価は、
元の raw (p,d) 剰余の single 対象に一致する。

## 方針
全有限 δ 深さの Koszul 分解と Tor の逐次余極限保存から全評価源の Tor 消滅を得る。
Tor の対称性と標準 augmentation を用い、通常の残余 tensor を同定する。

## 規約
hpR と正次数は不要であり、ねじれ除去商へ置き換えない。

## 使われ方
元の実完備化の hpR なしの導来剰余計算へ渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P₁" => PowerRootPolynomial A p hp
local notation "E₁" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A P₁ d
local notation "c₁" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L₁" => PowerRootUnaryFreeDeltaRing A p hp
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C dP}
local notation "ψ₁" => RingHom.comp (Ideal.Quotient.mk K₁) (deltaDivisionSourceMap E₁ dP)
local notation "β₁" => deltaDivisionSourceEval E₁ c₁
local notation "Mψ" => baseChangeScalarModule ψ₁
local notation "Mβ" => baseChangeScalarModule β₁

set_option maxHeartbeats 800000 in
-- 無限根環と自由 δ 環に沿う二つの制限係数構造を Tor 比較で照合するため。
include hf in
/-- 概要：Tor対称性で、同じ実残余終域をβに沿って導来拡大するための消滅条件を得る。
方針：有限 δ 深さの Tor 消滅を既存の逐次余極限と Tor 対称性で移す。
規約：元の一元入力を固定し、hpR と正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の標準導来 augmentation の入力。 -/
theorem powerRootPrismMonicResidueSourceEval_torVanishing_of_unconditional :
    scalarExtensionTorVanishing β₁ Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := deltaDivisionSourceEvaluationAlgebra E₁ c₁
      let : Subsingleton (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        powerRootPrismMonicResidueSource_tor_subsingleton_of_unconditional W hW f hf i
      have hz : IsZero (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (derivedModuleBaseChangeHomologyIso ψ₁ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars ψ₁).map_isZero hzH
      have hzT := ((derivedModuleBaseChangeTorIso ψ₁ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT


local notation "Q₁" => L₁ ⧸ K₁
local notation "Res₁" => DeltaAdjoinDivisionResidue E₁ dP c₁

include hf in
/-- 概要：無限根モニック入力の実残余終域の導来評価は raw (p,d) 商の次数零対象と標準同型。
方針：高次 Tor 消滅による標準 augmentation と、通常残余テンソルの既存同型を合成する。
規約：同じ元の自由 δ 源射と評価射を使う。
使われ方：BS Rem 7.15（著者版 p.62）の係数側の実導来剰余比較。 -/
def powerRootPrismMonicResidueSourceDerivedIso_of_unconditional :
    (boundedAboveDerivedBaseChange β₁).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₁ Res₁) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₁ c₁
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := PUnit.{u + 1}) E₁ dP
  letI : Module L₁ Q₁ := Algebra.toModule
  let e₁ : ((ModuleCat.extendScalars β₁).obj Mψ) ≃ₗ[P₁] (P₁ ⊗[L₁] Q₁) :=
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e := e₁.trans
    (deltaDivisionSourceResidueTensorAlgEquiv E₁ dP c₁).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₁ Mψ
    (powerRootPrismMonicResidueSourceEval_torVanishing_of_unconditional W hW f hf) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

end SerrePositivity.BhattScholze.Andre

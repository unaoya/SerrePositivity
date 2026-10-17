module

public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootResidueSource
public import SerrePositivity.BhattScholze.Andre.MonicPrismaticCoefficientReduction

/-!
# 元の無限根入力の実係数還元の無条件比較

## 概要
BS Rem 7.15（著者版 p.62）の元の自由 δ 源上の実導来還元を、同じ raw 残余商へ比較する。

## 方針
hpR なしの実導来評価比較と、商射の全射性による係数作用の降下を用いる。

## 規約
モニック性のみを保持し、元の自由環・raw 商を変更しない。

## 使われ方
元の A 上への係数制限と実逐次完備化の hpR 解消へ渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P₀" => PowerRootPolynomial A p hp
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "E₀" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P₀ W.generator
local notation "c₀" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap E₀ dP
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ dP c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ dP c₀
local notation "r₀" => Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal E₀ dP c₀)

/-- 概要：一般モニック f/d 包の自由 δ 源上の三因子導来還元対象。
方針：評価・除算の二因子導来テンソルを実 (p,d) 商のスカラー対象とテンソルする。
規約：導来還元の実対象を明示する。平坦性は定義に含めない。
使われ方：BS Rem 7.15（著者版 p.62）の実商還元を raw 剰余へ比較する。 -/
abbrev PowerRootPrismMonicSourceCoefficientReduced_of_unconditional :=
  boundedAboveDerivedTensor.obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
        derivedBaseChangeScalarObject q₀)

/-- 概要：無限根モニック入力について、係数商による実三因子還元は既存raw(p,d)商の次数零対象に一致する。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：完全 prism とモニック性のみを仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数商への実還元。 -/
def powerRootPrismMonicSourceCoefficientResidueIso_of_unconditional (hf : f.Monic) :
    PowerRootPrismMonicSourceCoefficientReduced_of_unconditional W hW f ≅
      boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := deltaDivisionSourceResidueAssociatorReductionIso E₀ dP c₀
  let e₂ := (boundedAboveDerivedBaseChangeTensorIso β₀
    (boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (boundedAboveDerivedRestrictScalars β₀).mapIso
    (powerRootPrismMonicResidueSourceDerivedIso_of_unconditional W hW f hf)
  let e₄ : (boundedAboveDerivedRestrictScalars β₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀)) ≅
        boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((derivedRestrictScalarsSingleIso β₀ 0).app (ModuleCat.of P₀ Res₀))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 概要：実係数還元のH0は、βによる実源作用を持つ既存raw残余商と加群同型。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：完全 prism とモニック性のみを仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数商への実還元。 -/
def powerRootPrismMonicSourceCoefficientResidueHomologyZeroIso_of_unconditional (hf : f.Monic) :
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).obj
      (PowerRootPrismMonicSourceCoefficientReduced_of_unconditional W hW f).obj) ≅ MRes :=
  (((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (powerRootPrismMonicSourceCoefficientResidueIso_of_unconditional W hW f hf))) ≪≫
        (realizedSingleH0Iso L₀).app MRes)

/-- 概要：実係数商還元の非零次数ホモロジーは、同じ明示入力の下で零。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：完全 prism とモニック性のみを仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数商への実還元。 -/
theorem powerRootPrismMonicSourceCoefficientResidue_homology_isZero_of_unconditional
    (hf : f.Monic)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).obj
      (PowerRootPrismMonicSourceCoefficientReduced_of_unconditional W hW f).obj) :=
  (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceCoefficientResidueIso_of_unconditional W hW f hf)))


end SerrePositivity.BhattScholze.Andre

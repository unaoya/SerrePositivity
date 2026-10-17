module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticSourceResidue
public import SerrePositivity.BhattScholze.DeltaDivisionSourceCoefficientRightFactor

/-!
# André E1・E2：モニック族の係数側の実導来剰余比較

## 概要

有限モニック族の f/d 包の自由 δ 源上の実三因子還元は、実 raw (p,d) 剰余の single に同型。
BS Rem 7.15（著者版 p.62）の元の係数環への比較の準備。

## 方針

既存の一般結合子と右因子の商比較、前工程の標準導来評価比較を合成する。
原典の Prop 7.11 を使う証明とは異なる実関係による計算。

## 規約

正次数は不要。元の係数作用を保つ具体的な導来同型を構成する。

## 使われ方

実自由 δ 源の商上へ作用を降下し、元の A/(p,d) 上でのホモロジーを計算する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) {m : ℕ}
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)

/-- 概要：一般モニック f/d 包の自由 δ 源上の三因子導来還元対象。
方針：評価・除算の二因子導来テンソルを実 (p,d) 商のスカラー対象とテンソルする。
規約：導来還元の実対象を明示する。平坦性は定義に含めない。
使われ方：BS Rem 7.15（著者版 p.62）の実商還元を raw 剰余へ比較する。 -/
abbrev MonicPrismaticSourceCoefficientReduced :=
  boundedAboveDerivedTensor.obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
        derivedBaseChangeScalarObject q₀)

/-- 概要：有限モニック族について、係数商による実三因子還元は既存raw(p,d)商の次数零対象に一致する。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：有限全列挙、モニック性、係数環の p 正則性、δ(d) の単元性を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数商への実還元。 -/
def monicPrismaticSourceCoefficientResidueIso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    MonicPrismaticSourceCoefficientReduced D d f ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := deltaDivisionSourceResidueAssociatorReductionIso E₀ (MvPolynomial.C d) c₀
  let e₂ := (boundedAboveDerivedBaseChangeTensorIso β₀
    (boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (boundedAboveDerivedRestrictScalars β₀).mapIso
    (monicPrismaticResidueSourceDerivedIso D d f s hf hpA v hv)
  let e₄ : (boundedAboveDerivedRestrictScalars β₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀)) ≅
        boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((derivedRestrictScalarsSingleIso β₀ 0).app (ModuleCat.of P₀ Res₀))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 概要：実係数還元のH0は、βによる実源作用を持つ既存raw残余商と加群同型。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：有限全列挙、モニック性、係数環の p 正則性、δ(d) の単元性を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数商への実還元。 -/
def monicPrismaticSourceCoefficientResidueHomologyZeroIso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).obj
      (MonicPrismaticSourceCoefficientReduced D d f).obj) ≅ MRes :=
  (((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (monicPrismaticSourceCoefficientResidueIso D d f s hf hpA v hv))) ≪≫
        (realizedSingleH0Iso L₀).app MRes)

/-- 概要：実係数商還元の非零次数ホモロジーは、同じ明示入力の下で零。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：有限全列挙、モニック性、係数環の p 正則性、δ(d) の単元性を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数商への実還元。 -/
theorem monicPrismaticSourceCoefficientResidue_homology_isZero
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).obj
      (MonicPrismaticSourceCoefficientReduced D d f).obj) :=
  (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCoefficientResidueIso D d f s hf hpA v hv)))

end SerrePositivity.BhattScholze.Andre

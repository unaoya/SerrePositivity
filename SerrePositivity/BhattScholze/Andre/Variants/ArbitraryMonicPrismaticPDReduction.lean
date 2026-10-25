module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticPDReduction
public import SerrePositivity.BhattScholze.Andre.Variants.ArbitraryMonicPrismaticQuotientFlat

/-!
# André E1・E2（任意族）：元の係数環上の実 (p,d) 還元と raw 残余商

## 概要

任意正次数モニック族の f/d 源の実 (p,d) 還元は離散的で、H⁰ が元の A/(p,d) 上忠実平坦。
BS Rem 7.15（著者版 p.62）の元の係数作用を保つ剰余計算。

## 方針

二重多項式係数包含の一般導来正方形比較を再利用し、実源商上で得た同型と忠実平坦性を移す。
原典の Prop 7.11 を使う証明とは異なる経路の計算。

## 規約

離散性には正次数は不要。完備化後の離散性は別工程。

## 使われ方

実逐次 p,d 完備化と、その生成元冪商への還元の入力。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

local notation "LCoef" => algebraMap A L₀
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "X₀" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)



local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀))
  (MonicPrismaticSourceCoefficientObject D d f)

/-- 概要：元のA上の実モニック族添加対象の実(p,d)還元と、作用を制限したraw商のsingle比較。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def monicPrismaticSourceCoefficientPDResidueIso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Y₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact monicPrismaticSourceCoefficientPDReductionIso D d f ≪≫
    (boundedAboveDerivedRestrictScalars κ₀).mapIso
      (monicPrismaticSourceQuotientDerivedSingleIso_arbitrary D d f hf hpA v hv) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ₀ 0).app (ModuleCat.of Q₀ Res₀))

/-- 概要：元のA上の実還元のH0と、標準係数作用を制限したraw商の加群同型。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def monicPrismaticSourceCoefficientPDResidueH0Iso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅ MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCoefficientPDResidueIso_arbitrary D d f hf hpA v hv)) ≪≫
    (realizedSingleH0Iso R₀).app MRes

/-- 概要：元のA上の実(p,d)還元の非零次数ホモロジーは零。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
theorem monicPrismaticSourceCoefficientPDResidue_homology_isZero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Y₀).obj) := by
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCoefficientPDResidueIso_arbitrary D d f hf hpA v hv)))

/-- 概要：元のA上の実(p,d)還元のH0は、実係数商A/(p,d)上忠実平坦。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
theorem monicPrismaticSourceCoefficientPDResidueH0_faithfullyFlat_arbitrary
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat R₀
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅
      (ModuleCat.restrictScalars κ₀).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (MonicPrismaticSourceQuotientDerived D d f).obj) :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceCoefficientPDReductionIso D d f)) ≪≫
    (derivedRestrictScalarsHomologyIso κ₀ 0).app (MonicPrismaticSourceQuotientDerived D d f).obj
  have := monicPrismaticSourceQuotientDerivedH0_faithfullyFlat_arbitrary
    D d f hf hdeg hpA v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticIteratedResidue
public import SerrePositivity.BhattScholze.Andre.Variants.ArbitraryMonicPrismaticPDReduction

/-!
# André E1・E2（任意族）：実逐次 p,d 完備化後のモニック源の剰余

## 概要

任意正次数モニック族の f/d 源を p,d の順に実導来完備化した対象の実 (p,d) 還元は
離散的で、H⁰ は元の A/(p,d) 上忠実平坦。BS Rem 7.15（著者版 p.62）の準備。

## 方針

p と d の個別の正則性により一般の逐次完備化単位比較を用い、元の実剰余計算へ戻す。
原典の Prop 7.11 を使う証明とは異なる経路の計算。

## 規約

d mod p の正則性は仮定しない。実完備化対象自体の離散性はまだ主張しない。

## 使われ方

冪零厚化と生成元冪商上の導来完備 Nakayama 判定へ渡す。
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
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => MonicPrismaticSourceCoefficientObject D d f
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)




/-- 概要：任意モニック族について、逐次主元完備化後の実還元は標準作用付きraw残余商のsingle対象。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、任意モニック族を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
def monicPrismaticSourceIteratedPDResidueIso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj (MonicPrismaticSourceIteratedPDCompletion D d f) ≅
      boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact monicPrismaticSourceIteratedPDReductionIso D d f hpA hd ≪≫
    monicPrismaticSourceCoefficientPDResidueIso_arbitrary D d f hf hpA v hv

/-- 概要：raw比較は合成標準単位の実還元を、未完備対象のraw比較へ送る。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、任意モニック族を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
theorem monicPrismaticSourceIteratedPDResidueIso_unit_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (monicPrismaticSourceIteratedPDResidueIso_arbitrary D d f hf hpA hd v hv).hom =
      (monicPrismaticSourceCoefficientPDResidueIso_arbitrary D d f hf hpA v hv).hom := by
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  simp only [monicPrismaticSourceIteratedPDResidueIso_arbitrary, Iso.trans_hom]
  rw [← Category.assoc, monicPrismaticSourceIteratedPDReductionIso_unit, Category.id_comp]

/-- 概要：逐次主元完備化後の実(p,d)還元の非零次数ホモロジーは零。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、任意モニック族を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
theorem monicPrismaticSourceIteratedPDResidue_homology_isZero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj) :=
  (monicPrismaticSourceCoefficientPDResidue_homology_isZero_arbitrary
    D d f hf hpA v hv i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (monicPrismaticSourceIteratedPDReductionIso D d f hpA hd)))

/-- 概要：逐次主元完備化後の実(p,d)還元のH0は、標準A/(p,d)上で忠実平坦。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、任意モニック族を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
theorem monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat_arbitrary
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat R₀ ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj X₀).obj :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceIteratedPDReductionIso D d f hpA hd))
  have := monicPrismaticSourceCoefficientPDResidueH0_faithfullyFlat_arbitrary
    D d f hf hdeg hpA v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

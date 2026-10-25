module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticCanonicalPowerResidue
public import SerrePositivity.BhattScholze.Andre.Variants.ArbitraryMonicPrismaticIteratedResidue

/-!
# André E1・E2（任意族）：モニック源の生成元冪商の標準冪零還元

## 概要

実逐次 p,d 完備化の A/(p,dⁿ) 還元を標準冪零商でさらに還元すると、
raw 剰余の係数作用を保つ single になる。BS Rem 7.15（著者版 p.62）の冪商計算。

## 方針

一般の冪零商・合成係数拡大の比較と、前工程の実 (p,d) 還元比較を合成する。
原典の Prop 7.11 を使う証明とは異なる経路の計算。

## 規約

n は正とする。二つの元の個別の正則性を使い、正則列とは仮定しない。

## 使われ方

冪零還元からの純性・平坦性の既存判定 G10 へ、同じ実対象の入力を渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) (n : ℕ) (hn : 0 < n)
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
local notation "X₀" => MonicPrismaticSourceIteratedPDCompletion D d f
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

local notation "qₙ" =>
  Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n))))
local notation "rₙ" => prismaticPowerResidueMap (p : A) d n hn
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange rₙ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀)

local notation "Tₙ" => A ⧸ Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "Sₙ" => Tₙ ⧸ Kₙ
local notation "eₙ" => prismaticPowerResidueQuotientEquiv (p : A) d n hn
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀
local notation "W₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Y₀
local notation "MCan" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars (RingEquiv.toRingHom eₙ)) MRes

/-- 概要：G10の標準冪零商による実還元は、商環上の標準raw加群のsingle対象。
方針：標準冪零商の一般比較と、元の (p,d) 還元の実 single 比較を合成する。
規約：任意モニック族、p と d の個別の正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の冪零厚化による実剰余の離散・平坦性。 -/
def monicPrismaticSourceCanonicalPowerResidueIso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    W₀ ≅ boundedAboveDerivedSingleFunctor.obj MCan := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀ ≪≫
    (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).mapIso
      ((prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm ≪≫
        monicPrismaticSourceIteratedPDResidueIso_arbitrary D d f hf hpA hd v hv) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso (eₙ).toRingHom 0).app MRes)

include hn in
/-- 概要：標準冪零商による実還元の非零次数ホモロジーは零。
方針：標準冪零商の一般比較と、元の (p,d) 還元の実 single 比較を合成する。
規約：任意モニック族、p と d の個別の正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の冪零厚化による実剰余の離散・平坦性。 -/
theorem monicPrismaticSourceCanonicalPowerResidue_homology_isZero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (W₀).obj) := by
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MCan i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCanonicalPowerResidueIso_arbitrary
          D d f n hn hf hpA hd v hv)))

include hn in
/-- 概要：標準冪零商による実還元のH0は、その正確な商環上で忠実平坦。
方針：標準冪零商の一般比較と、元の (p,d) 還元の実 single 比較を合成する。
規約：任意モニック族、p と d の個別の正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS Rem 7.15（著者版 p.62）の冪零厚化による実剰余の離散・平坦性。 -/
theorem monicPrismaticSourceCanonicalPowerResidueH0_faithfullyFlat_arbitrary
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Z₀).obj
  let eH : (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj ≅
      (ModuleCat.restrictScalars (eₙ).toRingHom).obj M :=
    (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀)) ≪≫
      (derivedRestrictScalarsHomologyIso (eₙ).toRingHom 0).app (Z₀).obj
  let := (eₙ).toRingHom.toAlgebra
  let : Module Sₙ M := Module.compHom M (eₙ).toRingHom
  let : IsScalarTower Sₙ R₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Sₙ ≃ₐ[Sₙ] R₀ :=
    AlgEquiv.ofBijective (Algebra.ofId Sₙ R₀) (eₙ).bijective
  have : Module.FaithfullyFlat Sₙ R₀ :=
    Module.FaithfullyFlat.of_linearEquiv Sₙ Sₙ eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat R₀ M := by
    let N := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj X₀).obj
    let eM : M ≅ N := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm)
    have : Module.FaithfullyFlat R₀ N :=
      monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat_arbitrary D d f hf hdeg hpA hd v hv
    exact Module.FaithfullyFlat.of_linearEquiv R₀ N eM.toLinearEquiv
  have : Module.FaithfullyFlat Sₙ M := Module.FaithfullyFlat.trans Sₙ R₀ M
  exact Module.FaithfullyFlat.of_linearEquiv Sₙ M eH.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

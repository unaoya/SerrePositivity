module

public import SerrePositivity.BhattScholze.Andre.Unconditional.PrimeReductionPurity
public import SerrePositivity.BhattScholze.Andre.Unconditional.CompletionTorsionDetection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionScalarConeComparison

/-!
# 元の raw 源の p 錐と d 完備化の純性

## 概要
BS Rem 7.15（著者版 p.62）の元の実源の先行 p 錐を d 完備化すると負次数は消える。

## 方針
p 完備化単位の p 錐同値性と、d 完備化と p 錐の可換性を合成する。
既証明の逐次完備化の p 還元純性を、元の対象の実 d 完備化へ移す。

## 規約
元の導来源を用い、hpR・raw p 正則性・d mod p 正則性を要求しない。

## 使われ方
局所化側と組み合わせて元の raw 源の p 正則性を検出する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：元の b 錐の a 完備化は、b 完備化後の a 完備化の b 錐と同型。
方針：b 完備化単位の b 錐同値と a 完備化の錐比較を合成する。
規約：a,b の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の先行 p 錐の純性。 -/
def unconditionalIteratedCompletion_scalarConeIso
    {R : Type u} [CommRing R] (a b : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (derivedComplexCompletionFunctor R a).obj ((derivedScalarConeFunctor R b).obj X.obj) ≅
      (derivedScalarConeFunctor R b).obj
        ((boundedAboveDerivedCompletionFunctor R a).obj
          ((boundedAboveDerivedCompletionFunctor R b).obj X)).obj := by
  let η := (derivedComplexCompletionUnit R b).app X.obj
  have hη := derivedScalarCone_map_isIso_of_completion R b η
    (derivedComplexCompletionFunctor_map_unit_isIso R b X.obj) 1
  rw [pow_one] at hη
  have := hη
  exact (derivedComplexCompletionFunctor R a).mapIso
      (asIso ((derivedScalarConeFunctor R b).map η)) ≪≫
    completionScalarConeIso R a b ((boundedAboveDerivedCompletionFunctor R b).obj X)

/-- 概要：正則主元での実導来商の負次数消滅は、同じ実スカラー錐の負次数消滅を与える。
方針：実 Koszul 比較と正確な係数制限のホモロジー比較を使う。
規約：正則性は係数環上の主元だけに課す。
使われ方：BS Rem 7.15（著者版 p.62）の既証明の p 還元純性の移送。 -/
theorem unconditionalScalarCone_isGE_of_regular_quotient_isGE
    {R : Type u} [CommRing R] (b : R) (hb : IsSMulRegular R b)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (h : ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj X).obj.IsGE 0) :
    ((derivedScalarConeFunctor R b).obj X.obj).IsGE 0 := by
  let q := Ideal.Quotient.mk (Ideal.span {b})
  let Y := ((boundedAboveDerivedBaseChange q).obj X).obj
  apply (DerivedCategory.isGE_iff _ 0).mpr
  intro i hi
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      (restrictedDerivedQuotientKoszulIso b hb X).symm ≪≫
    (derivedRestrictScalarsHomologyIso q i).app Y
  exact ((ModuleCat.restrictScalars q).map_isZero
    ((DerivedCategory.isGE_iff Y 0).mp h i hi)).of_iso e

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)

/-- 概要：元の実源の先行 p 錐の d 完備化は負次数を持たない。
方針：逐次完備化の p 還元純性を、元の実 p 錐と d 完備化の比較で移す。
規約：hpR・raw p 正則性は不要。元の標準 A 作用を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の局所化と完備化による raw 正則性検出。 -/
theorem powerRootPrismMonicSourcePrimeConeCompletion_isGE_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ((derivedComplexCompletionFunctor A W.generator).obj
      ((derivedScalarConeFunctor A (p : A)).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f).obj)).IsGE 0 := by
  let X := PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f
  let XC := PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f
  let e := unconditionalIteratedCompletion_scalarConeIso W.generator (p : A) X
  have h := unconditionalScalarCone_isGE_of_regular_quotient_isGE (p : A)
    hW.p_mul_injective XC
    (powerRootPrismMonicSourcePrimeReduction_pure_of_unconditional W hW f hf hdeg).1
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm 0

end SerrePositivity.BhattScholze.Andre

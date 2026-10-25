module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PrincipalSourceRegularity

/-!
# 元の第一完備化の H⁰ と raw の主完備化

## 概要
BS Rem 7.15（著者版 p.62）の元の実源の第一 p 完備化の H⁰ を、raw 主完備化へ比較する。

## 方針
元の標準 augmentation、正確な係数制限と完備化の比較、実主 Koszul H⁰ 比較を合成する。

## 規約
元の標準 A 作用を保持する。モニック性・正次数は比較自体には不要。

## 使われ方
元の古典的 p 完備化へ分母正則性を移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hpNat
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "c" => algebraMap A Raw
local notation "X" => PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f
local notation "XP" => CategoryTheory.Functor.obj
  (boundedAboveDerivedCompletionFunctor A (p : A)) (X)

/-- 概要：元の実源の第一 p 完備化の H⁰ と、元の raw 主完備化の A 線形同型。
方針：元の標準 augmentation の完備化後 H⁰ 同型と、元の主完備化の比較を合成する。
規約：比較自体には raw p 正則性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の分母作用の元の古典的 p 完備化への移送。 -/
def powerRootPrismMonicSourcePrincipalH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XP).obj ≅
      (ModuleCat.restrictScalars c).obj
        (ModuleCat.of Raw (PrincipalCompletionH0 Raw (p : Raw))) := by
  let M := (DerivedCategory.singleFunctor (ModuleCat Raw) 0).obj (ModuleCat.of Raw Raw)
  let F := derivedComplexCompletionFunctor A (p : A)
  have hAug := powerRootPrismMonicSourceRawPComparison_h0_isIso_of_unconditional W hW f
  let eAug := asIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
    (((boundedAboveDerivedCompletionFunctor A (p : A)).map
      (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f)).hom))
  let eP := F.mapIso (powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional W hW f) ≪≫
    (derivedCompletionRestrictionIso c (p : A)).app M
  rw [map_natCast] at eP
  let eH := (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso eP ≪≫
    (derivedRestrictScalarsHomologyIso c 0).app
      ((derivedComplexCompletionFunctor Raw (p : Raw)).obj M)
  let eN : (DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
      ((derivedComplexCompletionFunctor Raw (p : Raw)).obj M) ≅
        ModuleCat.of Raw (PrincipalCompletionH0 Raw (p : Raw)) :=
    principalCompletedUnitH0Iso Raw (p : Raw)
  exact eAug ≪≫ eH ≪≫ (ModuleCat.restrictScalars c).mapIso eN

end SerrePositivity.BhattScholze.Andre

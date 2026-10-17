module

public import SerrePositivity.BhattScholze.Andre.Unconditional.RawPrimeRegularAllMonic
public import SerrePositivity.BhattScholze.Andre.Unconditional.SourceUnitSingle
public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootRawCompletionRestriction

/-!
# 元の第一完備化の分母正則性

## 概要
BS Rem 7.15（著者版 p.62）の元の実 p 完備化の H⁰ で分母は正則。

## 方針
d 完備化単位の実 d 錐同値性から、既証明の逐次完備化の分母正則性を戻す。

## 規約
元の実源と標準 A 作用を保持し、raw mod p の d 正則性を使わない。

## 使われ方
元の通常 p 完備化の分母正則性へ移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：完備化が正則主元を持つ single なら、元の H⁰ 上でも同じ主元は単射。
方針：元の完備化単位の Koszul 同値性と、加群上の正則主商の実錐比較を使う。
規約：元の対象の純性・完備性・環の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の第一完備化への分母正則性の移送。 -/
theorem unconditionalHomology_regular_of_completionSingleIso
    {R : Type u} [CommRing R] (a : R) (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (M : ModuleCat.{u} R)
    (e : (derivedComplexCompletionFunctor R a).obj X.obj ≅
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)
    (hM : IsSMulRegular M a) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => a • x) := by
  let η := (derivedComplexCompletionUnit R a).app X.obj
  have hη := derivedScalarCone_map_isIso_of_completion R a η
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj) 1
  rw [pow_one] at hη
  have := hη
  have eQ := derivedScalarConeModuleQuotientIso a M hM 1
  rw [pow_one] at eQ
  let eC := asIso ((derivedScalarConeFunctor R a).map η) ≪≫
    (derivedScalarConeFunctor R a).mapIso e ≪≫ eQ
  apply derived_homology_smul_injective_of_scalarCone_isZero a X.obj 0
  exact (derivedSingleHomology_isZero (modulePowerReduction a M 1) (0 - 1) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R) (0 - 1)).mapIso eC)

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "X" => PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f
local notation "XP" => CategoryTheory.Functor.obj
  (boundedAboveDerivedCompletionFunctor A (p : A)) (X)
local notation "XC" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f

/-- 概要：正次数モニック入力の元の実 p 完備化の H⁰ 上で分母は単射。
方針：同じ実源の逐次完備化の single 比較と分母正則性を一般の Koszul 比較へ渡す。
規約：hpR・raw mod p の分母正則性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の元の古典的 p 完備化の分母正則性。 -/
theorem powerRootPrismMonicSourcePCompletion_generator_injective_of_positive_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XP).obj => W.generator • x) :=
  unconditionalHomology_regular_of_completionSingleIso W.generator XP
    ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XC).obj)
    (powerRootPrismMonicSourceSingleIso_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicSourceIteratedPDCompletion_pure_regular_of_unconditional W hW f hf hdeg).2.2

end SerrePositivity.BhattScholze.Andre

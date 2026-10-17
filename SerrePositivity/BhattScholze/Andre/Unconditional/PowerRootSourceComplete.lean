module

public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootAResidue
public import SerrePositivity.BhattScholze.Andre.MonicPrismaticSourceComplete
public import SerrePositivity.BhattScholze.PrismaticCoefficientCompletionReduction

/-!
# 元の無限根源の実逐次完備性

## 概要
BS Rem 7.15（著者版 p.62）の元の A 上の無限根源を p,d の順に実導来完備化する。
生成元冪商への実還元も、その商環上で p 導来完備である。

## 方針
主元の導来完備化関手、錐と塔極限での完備性、正則主商の比較を使う。

## 規約
hpR とモニック性は不要。元の prism 生成元の正則性だけを内部で使う。

## 使われ方
A1-d の実残余 H⁰ の忠実平坦性を明示仮定として受け取り、純性へ進む。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "d" => W.generator
local notation "XB" => PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f

/-- 概要：元の無限根源を p 完備化してから生成元で完備化した実対象。
方針：二つの既存主元導来完備化関手を合成する。
規約：raw 包のねじれ除去商へ置き換えない。
使われ方：BS Rem 7.15（著者版 p.62）の hpR なしの実完備化の純性。 -/
abbrev PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional :=
  (boundedAboveDerivedCompletionFunctor A d).obj
    ((boundedAboveDerivedCompletionFunctor A (p : A)).obj XB)

/-- 概要：実p完備化後に実d完備化を施した具体的モニック族添加対象は、なおp導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：モニック性・正次数・hpR は不要。生成元の正則性は prism から供給する。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem powerRootPrismMonicSourceIteratedPDCompletion_isComplete_p_of_unconditional :
    DerivedCompletion.IsComplete A (p : A)
      (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj := by
  let X := PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f
  let Y := (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj X
  have hY : DerivedCompletion.IsComplete A (p : A) Y.obj :=
    DerivedCompletion.derivedComplexCompletionFunctor_isComplete A (p : A) X.obj
  let K := DerivedCategory.Q.objPreimage Y.obj
  let eK : DerivedCategory.Q.obj K ≅ Y.obj := DerivedCategory.Q.objObjPreimageIso Y.obj
  have hK : DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    DerivedCompletion.isComplete_of_iso A (p : A) eK.symm hY
  have hstage (n : ℕ) : DerivedCompletion.IsComplete A (p : A)
      (DerivedCategory.Q.obj (DerivedCompletion.complexPowerKoszulStage A d K n)) :=
    DerivedCompletion.isComplete_Q_mappingCone A (p : A)
      (smulId (d ^ n) K) hK hK
  have hC : DerivedCompletion.IsComplete A (p : A)
      (DerivedCompletion.complexCompletionObject A d K) :=
    DerivedCompletion.isComplete_complexTowerHomotopyLimitObject_of_stages A (p : A)
      (DerivedCompletion.complexPowerKoszulStage A d K)
      (DerivedCompletion.complexPowerKoszulTransition A d K) hstage
  let e : DerivedCompletion.complexCompletionObject A d K ≅
      (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj :=
    (DerivedCompletion.derivedComplexCompletionComparison A d).symm.app K ≪≫
      (DerivedCompletion.derivedComplexCompletionFunctor A d).mapIso eK
  exact DerivedCompletion.isComplete_of_iso A (p : A) e hC

/-- 概要：同じ具体的逐次対象は、最後の主元完備化によりd導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：モニック性・正次数・hpR は不要。生成元の正則性は prism から供給する。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem powerRootPrismMonicSourceIteratedPDCompletion_isComplete_d_of_unconditional :
    DerivedCompletion.IsComplete A d
      (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj :=
  DerivedCompletion.derivedComplexCompletionFunctor_isComplete A d
    ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
      (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)).obj

local notation "X₀" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f

/-- 概要：正則dの実冪商への基底変更を制限すると、候補の実dⁿ Koszul錐になる。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：モニック性・正次数・hpR は不要。生成元の正則性は prism から供給する。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
def powerRootPrismMonicSourceGeneratorPowerReductionKoszulIso_of_unconditional (n : ℕ) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj ≅
        (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).obj (X₀).obj :=
  restrictedDerivedQuotientKoszulIso (d ^ n)
    ((show IsSMulRegular A W.generator from W.generator_regular).pow n) X₀

/-- 概要：正則dの任意冪商での実導来還元をAへ制限した対象は、p導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：モニック性・正次数・hpR は不要。生成元の正則性は prism から供給する。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem powerRootPrismMonicSourceGeneratorPowerReduction_isComplete_p_of_unconditional
    (n : ℕ) :
    DerivedCompletion.IsComplete A (p : A)
      (((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj) := by
  let K := DerivedCategory.Q.objPreimage (X₀).obj
  let eK : DerivedCategory.Q.obj K ≅ (X₀).obj := DerivedCategory.Q.objObjPreimageIso (X₀).obj
  have hK : DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    DerivedCompletion.isComplete_of_iso A (p : A) eK.symm
      (powerRootPrismMonicSourceIteratedPDCompletion_isComplete_p_of_unconditional W hW f)
  have hC := DerivedCompletion.isComplete_Q_mappingCone A (p : A) (smulId (d ^ n) K) hK hK
  let e := powerRootPrismMonicSourceGeneratorPowerReductionKoszulIso_of_unconditional W hW f n ≪≫
    (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).mapIso eK.symm ≪≫
      (DerivedCompletion.derivedScalarConeComparison A (d ^ n)).app K
  exact DerivedCompletion.isComplete_of_iso A (p : A) e.symm hC

/-- 概要：正則生成元の任意冪商への実還元は、その商環上でp導来完備。n=0も含む。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：モニック性・正次数・hpR は不要。生成元の正則性は prism から供給する。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem powerRootPrismMonicSourceGeneratorPowerReduction_isComplete_over_quotient_of_unconditional
    (n : ℕ) :
    IsComplete (A ⧸ Ideal.span {d ^ n}) (p : A ⧸ Ideal.span {d ^ n})
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f)).obj := by
  let q := Ideal.Quotient.mk (Ideal.span {d ^ n})
  let T := A ⧸ Ideal.span {d ^ n}
  let Y := ((boundedAboveDerivedBaseChange q).obj
    (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f)).obj
  let F := derivedRestrictScalars q
  have hR : IsComplete A (p : A) (F.obj Y) :=
    powerRootPrismMonicSourceGeneratorPowerReduction_isComplete_p_of_unconditional W hW f n
  have hunitR : IsIso ((derivedComplexCompletionUnit A (p : A)).app (F.obj Y)) :=
    derivedComplexCompletionUnit_isIso_of_isComplete A (p : A) (F.obj Y) hR
  let e := derivedRestrictionCompletionIso q (p : A)
  have hc : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y) ≫
      e.hom.app Y) := by
    rw [derivedRestrictionCompletionIso_unit]
    exact hunitR
  have hm : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y)) :=
    IsIso.of_isIso_comp_right _ (e.hom.app Y)
  have hS : IsIso ((derivedComplexCompletionUnit T (q (p : A))).app Y) :=
    isIso_of_reflects_iso _ F
  have hcomplete := (isComplete_iff_derivedComplexCompletionUnit_isIso T (q (p : A)) Y).mpr hS
  simpa only [map_natCast] using hcomplete



local notation "R" => A ⧸ Ideal.span {(p : A), d}
local notation "q" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "XC" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f

/-- 概要：実逐次完備化の (p,d) 導来還元は元の実源の還元と同型。
方針：元の A での p と d の個別正則性を標準完備化単位の比較へ供給する。
規約：d mod p の正則性も hpR も仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の A1-d の実剰余入力を完備化後へ渡す。 -/
def powerRootPrismMonicSourceIteratedPDReductionIso_of_unconditional :
    (boundedAboveDerivedBaseChange q).obj XC ≅ (boundedAboveDerivedBaseChange q).obj XB :=
  prismaticCoefficientIteratedCompletionPairIso (p : A) d hW.p_mul_injective
    W.generator_regular XB

/-- 概要：実逐次完備化の (p,d) 還元の全非零次数は消える。
方針：完備化単位の実還元比較と、証明済みの元の源の消滅を合成する。
規約：モニック性だけを追加し、hpR は不要。
使われ方：BS Rem 7.15（著者版 p.62）の純性判定への実剰余入力。 -/
theorem powerRootPrismMonicSourceIteratedPDResidue_homology_isZero_of_unconditional
    (hf : f.Monic) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((boundedAboveDerivedBaseChange q).obj XC).obj) :=
  (powerRootPrismMonicSourceCoefficientPDResidue_homology_isZero_of_unconditional
    W hW f hf i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (powerRootPrismMonicSourceIteratedPDReductionIso_of_unconditional W hW f)))

/-- 概要：A1-d の元の H⁰ 忠実平坦性入力は、同じ元の作用で実逐次完備化後に移る。
方針：標準単位を保つ実剰余比較の H⁰ 線形同型で移送する。
規約：入力は A1-d への受渡し型そのものを明示仮定にし、証明済みとは扱わない。
使われ方：BS Rem 7.15（著者版 p.62）の純性と分母正則性への条件付き接続。 -/
theorem powerRootPrismMonicSourceIteratedPDResidueH0_faithfullyFlat_of_initialCoefficient
    (hFF : Module.FaithfullyFlat R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        ((boundedAboveDerivedBaseChange q).obj XB).obj)) :
    Module.FaithfullyFlat R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        ((boundedAboveDerivedBaseChange q).obj XC).obj) := by
  let N := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
    ((boundedAboveDerivedBaseChange q).obj XB).obj
  haveI : Module.FaithfullyFlat R N := hFF
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (powerRootPrismMonicSourceIteratedPDReductionIso_of_unconditional W hW f))
  exact Module.FaithfullyFlat.of_linearEquiv R N e.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

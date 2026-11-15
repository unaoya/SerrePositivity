module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Residue
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicSource
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue
public import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Localization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-!
# 無限根源の完備化比較と純性

## 概要
源の逐次完備性、モニック f/d 源と raw 包の完備化比較、raw PD 比較と完全忠実平坦性、源の純性と生成元の正則性、先行 p 還元と完備化の p 正則性、p 錐と d 完備化の純性。
BS 著者版 Remark 7.15 の根の包に使う、無限根源の完備化と純性の比較を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPrism`、`PowerRootEnvelope/PerfectionFaithful`、`PowerRootEnvelope/Unconditional/FrobeniusPD`、`PowerRootEnvelope/Unconditional/RawRegular`、`PowerRootEnvelope/VarpiComparison`。
-/

universe u

/-! ## 元の無限根源の実逐次完備性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の A 上の無限根源を p,d の順に実導来完備化する。
生成元冪商への実還元も、その商環上で p 導来完備である。

## 方針
主元の導来完備化関手、錐と塔極限での完備性、正則主商の比較を使う。

## 規約
hpR とモニック性は不要。元の prism 生成元の正則性だけを内部で使う。

## 使われ方
実剰余の比較 の実残余 H⁰ の忠実平坦性を明示仮定として受け取り、純性へ進む。
-/

@[expose] public noncomputable section PowerRootSourceComplete

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "d" => W.generator
local notation "XB" => PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f

/-- 概要：元の無限根源を p 完備化してから生成元で完備化した実対象。
方針：二つの既存主元導来完備化関手を合成する。
規約：raw 包のねじれ除去商へ置き換えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の hpR なしの実完備化の純性。 -/
abbrev PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional :=
  (boundedAboveDerivedCompletionFunctor A d).obj
    ((boundedAboveDerivedCompletionFunctor A (p : A)).obj XB)

/-- 概要：実p完備化後に実d完備化を施した具体的モニック族添加対象は、なおp導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：モニック性・正次数・hpR は不要。生成元の正則性は prism から供給する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
def powerRootPrismMonicSourceGeneratorPowerReductionKoszulIso_of_unconditional (n : ℕ) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj ≅
        (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).obj (X₀).obj :=
  restrictedDerivedQuotientKoszulIso (d ^ n)
    ((show IsSMulRegular A W.generator from W.generator_regular).pow n) X₀

/-- 概要：正則dの任意冪商での実導来還元をAへ制限した対象は、p導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：モニック性・正次数・hpR は不要。生成元の正則性は prism から供給する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の 実剰余の比較 の実剰余入力を完備化後へ渡す。 -/
def powerRootPrismMonicSourceIteratedPDReductionIso_of_unconditional :
    (boundedAboveDerivedBaseChange q).obj XC ≅ (boundedAboveDerivedBaseChange q).obj XB :=
  prismaticCoefficientIteratedCompletionPairIso (p : A) d hW.p_mul_injective
    W.generator_regular XB

/-- 概要：実逐次完備化の (p,d) 還元の全非零次数は消える。
方針：完備化単位の実還元比較と、証明済みの元の源の消滅を合成する。
規約：モニック性だけを追加し、hpR は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の純性判定への実剰余入力。 -/
theorem powerRootPrismMonicSourceIteratedPDResidue_homology_isZero_of_unconditional
    (hf : f.Monic) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((boundedAboveDerivedBaseChange q).obj XC).obj) :=
  (powerRootPrismMonicSourceCoefficientPDResidue_homology_isZero_of_unconditional
    W hW f hf i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (powerRootPrismMonicSourceIteratedPDReductionIso_of_unconditional W hW f)))

/-- 概要：実剰余の比較 の元の H⁰ 忠実平坦性入力は、同じ元の作用で実逐次完備化後に移る。
方針：標準単位を保つ実剰余比較の H⁰ 線形同型で移送する。
規約：入力は 実剰余の比較 への受渡し型そのものを明示仮定にし、証明済みとは扱わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の純性と分母正則性への条件付き接続。 -/
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

end PowerRootSourceComplete

/-! ## 元の無限根源の純性と生成元の正則性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の実逐次完備化は次数零に集中し、生成元はその H⁰ に正則。

## 方針
実剰余の比較 の元の係数作用での忠実平坦性を受け取り、冪零還元、生成元冪商の有界 p ねじれ、
導来完備 Nakayama を順に使う。原典の p 正則基底への帰着とは異なる経路。

## 規約
hpR は仮定せず、元の源とその実完備化を使う。

## 使われ方
元の H の分母正則性と完全平坦性への作用を保つ比較に渡す。
-/

@[expose] public noncomputable section PowerRootSourcePurity

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "d" => W.generator
local notation "XC" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f
local notation "R₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
variable (n : ℕ) (hn : 0 < n)
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), d ^ n}
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "Sₙ" => Qₙ ⧸ Kₙ
local notation "qₙ" => Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n})
local notation "rₙ" => prismaticPowerResidueMap (p : A) d n hn
local notation "eₙ" => prismaticPowerResidueQuotientEquiv (p : A) d n hn
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) XC
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange rₙ) Y₀
local notation "WC" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Y₀

/-- 概要：標準冪零還元は元の (p,d) 還元の係数制限。
方針：実係数拡大の合成比較と標準商環同型を合成する。
規約：完全 prism の同じ実逐次完備化を使用する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪零厚化での純性判定。 -/
def powerRootPrismMonicSourceCanonicalPowerResidueIso_of_unconditional :
    WC ≅ (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).obj
      ((boundedAboveDerivedBaseChange q₀).obj XC) :=
  prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀ ≪≫
    (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).mapIso
      (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn XC).symm

include hn in
/-- 概要：標準冪零還元の非零次数ホモロジーは零。
方針：元の残余比較と係数制限のホモロジー比較を使う。
規約：モニック性を仮定するが hpR は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪零還元判定への消滅入力。 -/
theorem powerRootPrismMonicSourceCanonicalPowerResidue_homology_isZero_of_unconditional
    (hf : f.Monic) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (WC).obj) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceCanonicalPowerResidueIso_of_unconditional W hW f n hn)) ≪≫
    (derivedRestrictScalarsHomologyIso (eₙ).toRingHom i).app
      ((boundedAboveDerivedBaseChange q₀).obj XC).obj
  exact ((ModuleCat.restrictScalars (eₙ).toRingHom).map_isZero
    (powerRootPrismMonicSourceIteratedPDResidue_homology_isZero_of_unconditional
      W hW f hf i hi)).of_iso e

include hn in
/-- 概要：標準冪零還元の H⁰ は忠実平坦。
方針：実剰余の比較 の無条件入力を実完備化へ移し、商環同型による係数制限へ移す。
規約：モニック正次数のみ追加し、別の忠実平坦性仮定を置かない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実生成元冪商の平坦性。 -/
theorem powerRootPrismMonicSourceCanonicalPowerResidueH0_faithfullyFlat_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (WC).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
    ((boundedAboveDerivedBaseChange q₀).obj XC).obj
  let eH := (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceCanonicalPowerResidueIso_of_unconditional W hW f n hn)) ≪≫
    (derivedRestrictScalarsHomologyIso (eₙ).toRingHom 0).app
      ((boundedAboveDerivedBaseChange q₀).obj XC).obj
  letI := (eₙ).toRingHom.toAlgebra
  letI : Module Sₙ M := Module.compHom M (eₙ).toRingHom
  letI : IsScalarTower Sₙ R₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Sₙ ≃ₐ[Sₙ] R₀ := AlgEquiv.ofBijective (Algebra.ofId Sₙ R₀) (eₙ).bijective
  letI : Module.FaithfullyFlat Sₙ R₀ :=
    Module.FaithfullyFlat.of_linearEquiv Sₙ Sₙ eA.symm.toLinearEquiv
  letI : Module.FaithfullyFlat R₀ M :=
    powerRootPrismMonicSourceIteratedPDResidueH0_faithfullyFlat_of_initialCoefficient W hW f
      (InitialCoefficient.sourceResidueH0_faithfullyFlat W hW f hf hdeg)
  letI : Module.FaithfullyFlat Sₙ M := Module.FaithfullyFlat.trans Sₙ R₀ M
  exact Module.FaithfullyFlat.of_linearEquiv Sₙ M eH.toLinearEquiv

include hn in
/-- 概要：実 A/(p,dⁿ) 還元は次数零に集中し H⁰ は平坦。
方針：標準冪零還元へ純性・平坦性判定を適用する。
規約：正の冪 n とモニック正次数のみを仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の mod p 入力。 -/
theorem powerRootPrismMonicSourcePowerResidue_pure_flat_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    (Y₀).obj.IsGE 0 ∧ (Y₀).obj.IsLE 0 ∧
      Module.Flat Qₙ ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Y₀).obj) := by
  letI := powerRootPrismMonicSourceCanonicalPowerResidueH0_faithfullyFlat_of_unconditional
    W hW f n hn hf hdeg
  exact derived_pure_flat_of_nilpotent_reduction Kₙ Y₀
    (powerRootPrismMonicSourceCanonicalPowerResidue_homology_isZero_of_unconditional
      W hW f n hn hf) inferInstance ⟨n, prismaticPowerResidueIdeal_pow (p : A) d n⟩

include hn in
/-- 概要：実冪剰余の非零次数ホモロジー消滅。
方針：純性の二つの t 構造境界から消滅を読む。
規約：hpR は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商計算。 -/
theorem powerRootPrismMonicSourcePowerResidue_homology_isZero_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Y₀).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    powerRootPrismMonicSourcePowerResidue_pure_flat_of_unconditional W hW f n hn hf hdeg
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

local notation "Tₙ" => A ⧸ Ideal.span {d ^ n}
local notation "ZN" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))) XC

include hn in
/-- 概要：実 A/(dⁿ) 還元は次数零に集中し H⁰ の p ねじれは有界。
方針：同じ実 mod p 還元の純性・平坦性、商上の導来完備性、有界ねじれ判定を合成する。
規約：raw p 正則性を仮定せず、生成元冪商の既存ねじれ評価を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化の純性と分母正則性。 -/
theorem powerRootPrismMonicSourceGeneratorPowerReduction_pure_bounded_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    (ZN).obj.IsGE 0 ∧ (ZN).obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ z : (DerivedCategory.homologyFunctor (ModuleCat Tₙ) 0).obj (ZN).obj,
          (p : Tₙ) ^ k • z = 0 → (p : Tₙ) ^ N • z = 0 := by
  apply derived_pure_bounded_torsion_of_complete_flat_reduction (p : Tₙ) ZN
  · intro i hi
    exact prismaticGeneratorPowerModP_homology_isZero p d n XC i
      (powerRootPrismMonicSourcePowerResidue_homology_isZero_of_unconditional
        W hW f n hn hf hdeg i hi)
  · exact prismaticGeneratorPowerModPH0_flat p d n XC
      (powerRootPrismMonicSourcePowerResidue_pure_flat_of_unconditional
        W hW f n hn hf hdeg).2.2
  · exact ⟨n, perfectPrism_generator_power_bounded_torsion_of_unconditional W hW n⟩
  · exact powerRootPrismMonicSourceGeneratorPowerReduction_isComplete_over_quotient_of_unconditional
      W hW f n

/-- 概要：元の実逐次完備化は次数零に集中し、生成元は H⁰ に正則。
方針：一乗生成元商の純性と d 導来完備性から、正則商による純性判定を使う。
規約：元の A 作用を保持し、hpR と raw p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の H の分母正則性への移送。 -/
theorem powerRootPrismMonicSourceIteratedPDCompletion_pure_regular_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    (XC).obj.IsGE 0 ∧ (XC).obj.IsLE 0 ∧
      Function.Injective
        (fun x : (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XC).obj => d • x) := by
  apply derived_pure_of_complete_regular_quotient_pure d W.generator_regular XC
    (powerRootPrismMonicSourceIteratedPDCompletion_isComplete_d_of_unconditional W hW f)
  intro i hi
  have h := powerRootPrismMonicSourceGeneratorPowerReduction_pure_bounded_of_unconditional
    W hW f 1 (by omega) hf hdeg
  have hd1 : W.generator ^ (1 : ℕ) = W.generator := _root_.pow_one _
  rw [hd1] at h
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact (DerivedCategory.isGE_iff _ _).mp h.1 i hlt
  · exact (DerivedCategory.isLE_iff _ _).mp h.2.1 i hgt

/-- 概要：元の実逐次完備化は同じ H⁰ の次数零対象と同型。
方針：証明済みの純性へ標準正規化比較を適用する。
規約：元の A 作用を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の raw PD 環への比較。 -/
def powerRootPrismMonicSourceSingleIso_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    (XC).obj ≅ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XC).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    powerRootPrismMonicSourceIteratedPDCompletion_pure_regular_of_unconditional W hW f hf hdeg
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso (XC).obj 0

end SerrePositivity.BhattScholze.Andre

end PowerRootSourcePurity

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

元の無限根モニック源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section PowerRootRawSourceComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
/-- 概要：通常テンソルの指定同型を標準導来 augmentation へ合成する。
方針：実テンソルの標準 H⁰ 比較を使う。
規約：モニック性・平坦性・有限性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の raw 実完備化との比較。 -/
def unconditionalTensorRawAugmentation {S : Type u} [CommRing S]
    (M N K : ModuleCat.{u} S) (e : (tensorLeft M).obj N ≅ K) :
    boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N) ⟶
        boundedAboveDerivedSingleFunctor.obj K := by
  let η : boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N) ⟶
        boundedAboveDerivedSingleFunctor.obj ((tensorLeft M).obj N) :=
    ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation M).app N)
  exact η ≫ boundedAboveDerivedSingleFunctor.map e.hom

/-- 概要：指定した標準 augmentation は H⁰ で同型を誘導する。
方針：実テンソルの標準 H⁰ 比較を使う。
規約：モニック性・平坦性・有限性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の raw 実完備化との比較。 -/
theorem unconditionalTensorRawAugmentation_h0_isIso {S : Type u} [CommRing S]
    (M N K : ModuleCat.{u} S) (e : (tensorLeft M).obj N ≅ K) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) 0).map
      (unconditionalTensorRawAugmentation M N K e).hom) := by
  have := derivedTensorAugmentation_h0_isIso M N
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) 0).map
    (((boundedAboveDerivedTensorModuleAugmentation M).app N) ≫
      (DerivedCategory.singleFunctor (ModuleCat S) 0).map e.hom))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 概要：二因子の実導来テンソルの H⁰ 比較は元の係数制限と両立する。
方針：実テンソルの標準 H⁰ 比較を使う。
規約：モニック性・平坦性・有限性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の raw 実完備化との比較。 -/
def unconditionalRestrictedTensorRawH0Iso {S T : Type u} [CommRing S] [CommRing T]
    (k : T →+* S) (M N K : ModuleCat.{u} S) (e : (tensorLeft M).obj N ≅ K) :
    (DerivedCategory.homologyFunctor (ModuleCat T) 0).obj
      ((boundedAboveDerivedRestrictScalars k).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))).obj ≅
      (ModuleCat.restrictScalars k).obj K :=
  (derivedRestrictScalarsHomologyIso k 0).app _ ≪≫
    (ModuleCat.restrictScalars k).mapIso
      ((boundedAboveDerivedTensorModuleH0NatIso M).app N ≪≫ e)

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat) d
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat
local notation "L" => PowerRootUnaryFreeDeltaRing A p hpNat
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "α" =>
  deltaDivisionSourceMap (σ := PUnit) E dP
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "Raw" => DeltaAdjoinDivision E dP r
local notation "X" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

/-- 概要：raw包に、評価βを経由する元の実源L作用を明示した加群対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def PowerRootPrismMonicSourceRawModule_of_unconditional : ModuleCat.{u} L := by
  let := deltaDivisionSourceRawAlgebra E dP r
  let : Module L Raw := Algebra.toModule
  exact ModuleCat.of L Raw

/-- 概要：通常二因子テンソルとraw包は、元の実源L上で線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional :
    (tensorLeft Mβ).obj Mα ≅ PowerRootPrismMonicSourceRawModule_of_unconditional W hW f := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := PUnit.{u + 1}) E dP
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E dP r
  let : Module L Raw := Algebra.toModule
  let e : P ⊗[L] L ≃ₐ[L] Raw :=
    AlgEquiv.ofRingEquiv (f := deltaDivisionSourceTensorEquiv E dP r) (by
      intro x
      change deltaDivisionSourceTensorEquiv E dP r
        (β x ⊗ₜ[L] 1) = (deltaAdjoinDivisionMap E dP r) (β x)
      rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one])
  exact e.toLinearEquiv.toModuleIso

set_option maxHeartbeats 100000 in
-- 二つの実係数作用と元の導来テンソル対象の型を同時に照合するため。
set_option backward.isDefEq.respectTransparency true in
/-- 概要：元の実導来二因子源から、raw次数零対象への標準augmentation。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawAugmentation_of_unconditional :
    X ⟶ boundedAboveDerivedSingleFunctor.obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f) := by
  with_reducible exact (unconditionalTensorRawAugmentation (S := L) Mβ Mα
    (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)
    (powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional W hW f))

set_option maxHeartbeats 100000 in
-- 二つの実係数作用と元の導来テンソル対象の型を同時に照合するため。
/-- 概要：元の実導来二因子源のH0と実源作用付きraw包の比較。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat L) 0).obj (X).obj ≅
      PowerRootPrismMonicSourceRawModule_of_unconditional W hW f :=
  (boundedAboveDerivedTensorModuleH0NatIso (R := L) Mβ).app Mα ≪≫
    powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional W hW f

set_option backward.isDefEq.respectTransparency true in
/-- 概要：raw標準augmentationはH0では同型である。高次の消滅はここでは主張しない。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawAugmentation_h0_isIso_of_unconditional :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
      (powerRootPrismMonicSourceRawAugmentation_of_unconditional W hW f).hom) := by
  unfold powerRootPrismMonicSourceRawAugmentation_of_unconditional
  with_reducible exact (unconditionalTensorRawAugmentation_h0_isIso (S := L) Mβ Mα
    (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)
    (powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional W hW f))

/-- 概要：元のAへ係数制限したraw次数零対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional :=
  (boundedAboveDerivedRestrictScalars C₀).obj
    (boundedAboveDerivedSingleFunctor.obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f))

set_option maxHeartbeats 100000 in
-- 元のテンソル対象の係数制限と実ホモロジーの型を同時に照合するため。
/-- 概要：元のAへ係数制限した実導来源のH0も、raw包の同じ係数制限と同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawCoefficientH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f).obj ≅
      (ModuleCat.restrictScalars C₀).obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f) :=
  unconditionalRestrictedTensorRawH0Iso C₀ Mβ Mα
    (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)
    (powerRootPrismMonicSourceOrdinaryTensorRawIso_of_unconditional W hW f)

/-- 概要：元のA上の実導来源からraw次数零対象への、同じ実係数制限による射。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional :
    PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f ⟶ PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f :=
  (boundedAboveDerivedRestrictScalars C₀).map (powerRootPrismMonicSourceRawAugmentation_of_unconditional W hW f)

local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- 概要：raw次数零対象へ元と同じp,d逐次実導来完備化を施した対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional :=
  (Cd).obj ((Cp).obj (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f))

/-- 概要：元の実逐次完備化源から、rawの同じ実逐次完備化への標準比較射。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawIteratedComparison_of_unconditional :
    PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f ⟶ PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f :=
  (Cd).map ((Cp).map (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f))

/-- 概要：完備化後の比較射は、元のp,d合成標準単位と可換。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawIteratedComparison_unit_of_unconditional :
    ((Up).app (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f) ≫
      (Ud).app ((Cp).obj (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f))) ≫
        powerRootPrismMonicSourceRawIteratedComparison_of_unconditional W hW f =
      powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f ≫
        ((Up).app (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f) ≫
          (Ud).app ((Cp).obj (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f))) := by
  let η := powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f
  have hp := (Up).naturality η
  have hd := (Ud).naturality ((Cp).map η)
  simp only [CategoryTheory.Functor.id_map] at hp hd
  dsimp only [powerRootPrismMonicSourceRawIteratedComparison_of_unconditional]
  rw [Category.assoc, ← hd, ← Category.assoc, ← hp, Category.assoc]

end SerrePositivity.BhattScholze.Andre

end PowerRootRawSourceComparison

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

元の無限根モニック源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section PowerRootSourceNonpositive

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
/-- 概要：二つの次数零加群の実導来テンソルは、係数制限後も非正次数にある。
方針：非正射影モデルのテンソルと正確な係数制限で計算する。
規約：平坦性・モニック性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の実源の H⁰ 完備化比較。 -/
theorem unconditionalRestrictedTensor_isLE_zero
    {S T : Type u} [CommRing S] [CommRing T] (k : T →+* S)
    (M N : ModuleCat.{u} S) :
    ((boundedAboveDerivedRestrictScalars k).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))).obj.IsLE 0 := by
  let Pβ := projectiveResolutionDerivedModel (projectiveResolution M)
  let Pα := projectiveResolutionDerivedModel (projectiveResolution N)
  let K := cochainTensor Pβ.complex Pα.complex
  let KR : CochainComplex (ModuleCat T) ℤ :=
    ((ModuleCat.restrictScalars k).mapHomologicalComplex (.up ℤ)).obj K
  have hβ : Pβ.complex.IsStrictlyLE 0 := Pβ.bounded
  have hα : Pα.complex.IsStrictlyLE 0 := Pα.bounded
  have hK : K.IsStrictlyLE 0 := by
    simpa only [add_zero] using cochainTensor_isStrictlyLE Pβ.complex Pα.complex 0 0
  have hKR : KR.IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ _).mpr
    intro i hi
    change IsZero ((ModuleCat.restrictScalars k).obj (K.X i))
    exact (ModuleCat.restrictScalars k).map_isZero (K.isZero_of_isStrictlyLE 0 i hi)
  let e : ((boundedAboveDerivedRestrictScalars k).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))).obj ≅
      DerivedCategory.Q.obj KR :=
    (derivedRestrictScalars k).mapIso
        (boundedAboveDerivedTensorModelIso
          (boundedAboveDerivedSingleFunctor.obj M)
          (boundedAboveDerivedSingleFunctor.obj N) Pβ Pα) ≪≫
      (derivedRestrictScalarsFactors k).app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0


variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat) d
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat
local notation "L" => PowerRootUnaryFreeDeltaRing A p hpNat
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "α" =>
  deltaDivisionSourceMap (σ := PUnit) E dP
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedTensor
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

set_option maxHeartbeats 800000 in
-- 元の係数作用を保って具体的な非正射影テンソルモデルを照合するため。
set_option backward.isDefEq.respectTransparency true in
/-- 概要：同じ元の実A対象は非正次数の対象であり、離散性や完備性は仮定しない。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional :
    (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f).obj.IsLE 0 := by
  with_reducible exact (unconditionalRestrictedTensor_isLE_zero (S := L) (T := A) C₀ Mβ Mα)

/-- 概要：元Aへ制限した同じ実二因子源は、全正次数でホモロジーが消える。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceCoefficient_homology_isZero_positive_of_unconditional (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f).obj) :=
  (DerivedCategory.isLE_iff _ _).mp (powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional W hW f) i hi

/-- 概要：同じaugmentationの終域である係数制限raw singleも非正次数である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawCoefficient_isLE_zero_of_unconditional :
    (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj.IsLE 0 := by
  let e : (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        ((ModuleCat.restrictScalars C₀).obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)) :=
    (derivedRestrictScalarsSingleIso C₀ 0).app (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f)
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 概要：元Aへ制限した標準augmentationそのものも、H0に同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawCoefficientAugmentation_h0_isIso_of_unconditional :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
      (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f).hom) := by
  let η := (powerRootPrismMonicSourceRawAugmentation_of_unconditional W hW f).hom
  let H := DerivedCategory.homologyFunctor (ModuleCat A) 0
  let e := derivedRestrictScalarsHomologyIso C₀ 0
  have hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map η) :=
    powerRootPrismMonicSourceRawAugmentation_h0_isIso_of_unconditional W hW f
  have hn := e.hom.naturality η
  simp only [Functor.comp_map] at hn
  have he : IsIso (H.map ((derivedRestrictScalars C₀).map η) ≫ e.hom.app _) := by
    rw [hn]
    infer_instance
  change IsIso (H.map ((derivedRestrictScalars C₀).map η))
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)

end SerrePositivity.BhattScholze.Andre

end PowerRootSourceNonpositive

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

元の無限根モニック源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section PowerRootSourceCompletionH0

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat) d
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d

/-- 概要：元の実係数源のp,d逐次実完備化も非正である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceIteratedPDCompletion_isLE_zero_of_unconditional :
    (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj.IsLE 0 := by
  apply DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional W hW f)

/-- 概要：raw係数対象の同じp,d逐次実完備化も非正である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawIteratedCompletion_isLE_zero_of_unconditional :
    (PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f).obj.IsLE 0 := by
  apply DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (powerRootPrismMonicSourceRawCoefficient_isLE_zero_of_unconditional W hW f)

/-- 概要：同じ元のaugmentationは、実p完備化後にもH0同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawPComparison_h0_isIso_of_unconditional :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (((Cp).map (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f)).hom)) := by
  exact DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A (p : A)
    (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f)
    (powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional W hW f)
    (powerRootPrismMonicSourceRawCoefficient_isLE_zero_of_unconditional W hW f)
    (powerRootPrismMonicSourceRawCoefficientAugmentation_h0_isIso_of_unconditional W hW f)

/-- 概要：既存の標準逐次完備化比較射そのものがH0同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicSourceRawIteratedComparison_h0_isIso_of_unconditional :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (powerRootPrismMonicSourceRawIteratedComparison_of_unconditional W hW f).hom) := by
  exact DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A d
    ((Cp).map (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f))
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (powerRootPrismMonicSourceCoefficient_isLE_zero_of_unconditional W hW f))
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (powerRootPrismMonicSourceRawCoefficient_isLE_zero_of_unconditional W hW f))
    (powerRootPrismMonicSourceRawPComparison_h0_isIso_of_unconditional W hW f)

/-- 概要：実逐次源のH0とrawの実逐次完備化のH0を、同じ標準比較射で同定する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawIteratedH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f).obj := by
  let := powerRootPrismMonicSourceRawIteratedComparison_h0_isIso_of_unconditional W hW f
  exact asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (powerRootPrismMonicSourceRawIteratedComparison_of_unconditional W hW f).hom)

end SerrePositivity.BhattScholze.Andre

end PowerRootSourceCompletionH0

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

元の無限根モニック源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section PowerRootRawCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat) d
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat
local notation "L" => PowerRootUnaryFreeDeltaRing A p hpNat
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "β" => deltaDivisionSourceEval E r
local notation "Raw" => DeltaAdjoinDivision E dP r
local notation "j" => deltaAdjoinDivisionMap E dP r
local notation "C₀" => algebraMap A L

/-- 概要：評価βを経由する制限作用と、raw環の標準A作用の恒等線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawCoefficientModuleIso_of_unconditional :
    (ModuleCat.restrictScalars C₀).obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f) ≅
      ModuleCat.of A Raw := by
  let e : (ModuleCat.restrictScalars C₀).obj (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f) ≃ₗ[A] Raw :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
        change Raw at x
        change j (β (MvPolynomial.C (algebraMap A P a))) * x = a • x
        rw [Algebra.smul_def, deltaDivisionSourceEval_C]
        rfl }
  exact e.toModuleIso

/-- 概要：元のAへの実係数制限後のraw対象を、標準A作用付きraw環の次数零対象へ戻す。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawCoefficientSingleIso_of_unconditional :
    PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A Raw) :=
  ObjectProperty.isoMk _
    ((derivedRestrictScalarsSingleIso C₀ 0).app (PowerRootPrismMonicSourceRawModule_of_unconditional W hW f) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
        (powerRootPrismMonicSourceRawCoefficientModuleIso_of_unconditional W hW f))

set_option maxHeartbeats 800000 in
-- 元の導来テンソルと二つの係数制限を H⁰ の型に明示して照合するため。
/-- 概要：元の実導来源のH0は、標準A作用付きraw r/d環と線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceRawStandardH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f).obj ≅ ModuleCat.of A Raw :=
  powerRootPrismMonicSourceRawCoefficientH0Iso_of_unconditional W hW f ≪≫ powerRootPrismMonicSourceRawCoefficientModuleIso_of_unconditional W hW f

end SerrePositivity.BhattScholze.Andre

end PowerRootRawCoefficients

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

元の無限根モニック源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section PowerRootRawCompletionRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat) d
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP r
local notation "c" => algebraMap A Raw
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat Raw) 0) (ModuleCat.of Raw Raw)
local notation "Cp" => derivedComplexCompletionFunctor A (p : A)
local notation "Cd" => derivedComplexCompletionFunctor A d
local notation "Bp" => derivedComplexCompletionFunctor Raw (c (p : A))
local notation "Bd" => derivedComplexCompletionFunctor Raw (c d)
local notation "Res" => derivedRestrictScalars c

/-- 概要：元のraw係数対象は、raw環自身のsingleを実係数射で制限した対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional :
    (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj ≅ (Res).obj M :=
  DerivedCategory.Minus.ι.mapIso (powerRootPrismMonicSourceRawCoefficientSingleIso_of_unconditional W hW f) ≪≫
    (algebraRestrictionSingleIso A Raw).symm

/-- 概要：raw環自身の二つの主元についての実逐次完備化。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional := (Bd).obj ((Bp).obj M)

/-- 概要：二度の係数制限と完備化の比較を同じ係数射に適用した、元のraw実逐次対象との同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional :
    (PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f).obj ≅
      (Res).obj (PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional W hW f) :=
  (Cd).mapIso ((Cp).mapIso (powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional W hW f)) ≪≫
    (Cd).mapIso ((derivedCompletionRestrictionIso c (p : A)).app M) ≪≫
    (derivedCompletionRestrictionIso c d).app ((Bp).obj M)

/-- 概要：係数比較は両方の元の主元完備化単位を保つ。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem powerRootPrismMonicRawIteratedRestrictionIso_unit_of_unconditional :
    ((derivedComplexCompletionUnit A (p : A)).app
        (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj ≫
      (derivedComplexCompletionUnit A d).app
        ((Cp).obj (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj)) ≫
      (powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional W hW f).hom =
    (powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional W hW f).hom ≫
      (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M ≫
        (derivedComplexCompletionUnit Raw (c d)).app ((Bp).obj M)) := by
  let e := powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional W hW f
  let eP := (Cp).mapIso e ≪≫ (derivedCompletionRestrictionIso c (p : A)).app M
  have hp : (derivedComplexCompletionUnit A (p : A)).app
      (PowerRootPrismMonicSourceRawCoefficientObject_of_unconditional W hW f).obj ≫ eP.hom =
      e.hom ≫ (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M) := by
    have hn := (derivedComplexCompletionUnit A (p : A)).naturality e.hom
    simp only [Functor.id_map] at hn
    dsimp only [eP, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← hn, Category.assoc]
    erw [derivedCompletionRestrictionIso_unit]
  have hd := (derivedComplexCompletionUnit A d).naturality eP.hom
  simp only [Functor.id_map] at hd
  have he : (powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional W hW f).hom =
      (Cd).map eP.hom ≫ (derivedCompletionRestrictionIso c d).hom.app ((Bp).obj M) := by
    simp only [powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional, eP, e, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rfl
  rw [he]
  simp only [Category.assoc]
  rw [← Category.assoc ((derivedComplexCompletionUnit A d).app _) ((Cd).map eP.hom),
    ← hd]
  simp only [Category.assoc]
  erw [derivedCompletionRestrictionIso_unit]
  rw [← Category.assoc, hp, Category.assoc, ← Functor.map_comp]

/-- 概要：raw環上の同じ実逐次完備化のH0へ、元のA作用を保って比較する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicRawIteratedRestrictionH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (PowerRootPrismMonicSourceRawIteratedCompletion_of_unconditional W hW f).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional W hW f)) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso
    (powerRootPrismMonicRawIteratedRestrictionIso_of_unconditional W hW f) ≪≫
      (derivedRestrictScalarsHomologyIso c 0).app _

/-- 概要：元の実モニック族添加源のH0をraw環上の実逐次完備化のH0と同定する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def powerRootPrismMonicSourceInternalRawH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional W hW f)) :=
  powerRootPrismMonicSourceRawIteratedH0Iso_of_unconditional W hW f ≪≫ powerRootPrismMonicRawIteratedRestrictionH0Iso_of_unconditional W hW f

end SerrePositivity.BhattScholze.Andre

end PowerRootRawCompletionRestriction

/-! ## モニック源の実 H⁰ と raw PD 完備化環の比較

## 概要

元の無限根モニック源の実逐次 p,d 完備化の H⁰ は、raw f/d 包の実 PD 完備化 H⁰ と A 線形同型。
BS 著者版 Remark 7.15（著者版 p.62）の実源と環候補の比較。

## 方針

源の標準 augmentation の H⁰ 比較、係数制限と完備化の比較 の係数制限比較、既存の一般二座標 H⁰ 反射比較を合成する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる具体的係数射を保つ計算。

## 規約

モニック性・正次数・有限性はこの比較には不要。高次消滅は別に証明済みの純性から得る。

## 使われ方

完全 prism 上の無限根族の実源の離散性から、raw PD 環の元の係数射の完全忠実平坦性へ移す。
-/

@[expose] public noncomputable section PowerRootRawPDComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "D" => W.deltaStructure
local notation "d" => W.generator
local notation "dP" => algebraMap A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat) d
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "a" => c (p : A)
local notation "Z" => PowerRootPrismMonicRawInternalIteratedCompletion_of_unconditional W hW f
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat Raw) 0)

/-- 概要：raw 包自身の逐次実完備化 H⁰ は、元の Raw 線形単位を保って PD 完備化 H⁰ と同型。
方針：一般二座標 H⁰ 反射の既存比較をそのまま適用する。
規約：第一座標の像が自然数 p であることを明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実源から環候補への比較の最終段。 -/
def powerRootPrismMonicRawInternalPDLinearEquiv_of_unconditional : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z :=
  _root_.SerrePositivity.DerivedCompletion.iteratedPDH0LinearEquiv Raw a z p (map_natCast c p)

/-- 概要：raw 自身の比較は、すべての raw 係数の元の標準完備化像を保つ。
方針：一般 H⁰ 反射比較の標準単位公式を再利用する。
規約：単位 1 だけでなく任意の raw 元で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の候補係数射との後続比較。 -/
theorem powerRootPrismMonicRawInternalPDLinearEquiv_unit_of_unconditional (x : Raw) :
    powerRootPrismMonicRawInternalPDLinearEquiv_of_unconditional W hW f (_root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit Raw a z x) =
      pairCompletionH0Unit Raw (p : Raw) z x :=
  _root_.SerrePositivity.DerivedCompletion.iteratedPDH0LinearEquiv_unit Raw a z p (map_natCast c p) x

/-- 概要：元の実モニック源の逐次完備化 H⁰ は、raw PD 環の同じ A 係数制限と同型。
方針：標準 augmentation、二度の 係数制限と完備化の比較、Raw 線形 H⁰ 反射比較を順に合成する。
規約：元の A 作用を保つ加群同型を構成する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の環候補の完全忠実平坦性への移送。 -/
def powerRootPrismMonicSourcePDH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f).obj ≅
      (ModuleCat.restrictScalars c).obj (ModuleCat.of Raw (PDCompletionH0 Raw p z)) :=
  powerRootPrismMonicSourceInternalRawH0Iso_of_unconditional W hW f ≪≫
    (ModuleCat.restrictScalars c).mapIso
      (powerRootPrismMonicRawInternalPDLinearEquiv_of_unconditional W hW f).toModuleIso

end SerrePositivity.BhattScholze.Andre

end PowerRootRawPDComparison

/-! ## 有限モニック族の raw 実 PD 環の完全忠実平坦性

## 概要

完全 prism 上の正次数モニック無限根族の raw f/d 包の実 PD 完備化環は、元の (p,d) に関して
完全忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の環候補への平坦性の移送。

## 方針

同じ実源の離散性と、元の係数作用を保つ H⁰ 比較から raw PD 環の single 比較を構成する。
実剰余の Tor 消滅と忠実平坦性を完全忠実平坦性の一般判定へ渡す。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる経路の計算。

## 規約

この raw PD 環の完全 δ 化と最終 perfectoid 商への比較は別工程。

## 使われ方

完全 δ 化と実完備化の既存比較を介して、最終根付き perfectoid 候補の平坦性へ進む。
-/

@[expose] public noncomputable section PowerRootRawPDCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
variable (hf : f.Monic) (hdeg : 0 < f.natDegree)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "d" => W.generator
local notation "dP" => algebraMap A P d
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP r
local notation "c" => algebraMap A Raw
local notation "B" => PDCompletionH0 Raw p (c d)
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "X" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (boundedAboveDerivedSingleFunctor.obj M)
include hf hdeg

/-- 概要：元の実逐次源は、標準A作用付きraw PD環のsingle対象と同型。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
def powerRootPrismMonicSourcePDSingleIso_of_unconditional : X ≅ boundedAboveDerivedSingleFunctor.obj M :=
  ObjectProperty.isoMk _ (powerRootPrismMonicSourceSingleIso_of_unconditional W hW f hf hdeg ≪≫
    (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso (powerRootPrismMonicSourcePDH0Iso_of_unconditional W hW f))

/-- 概要：実PD環の同じ(p,d)導来還元の非零次数は消える。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_reduction_homology_isZero_of_unconditional (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  have hz := powerRootPrismMonicSourceIteratedPDResidue_homology_isZero_of_unconditional W hW f hf i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      ((boundedAboveDerivedBaseChange q).mapIso
        (powerRootPrismMonicSourcePDSingleIso_of_unconditional W hW f hf hdeg)))).symm

/-- 概要：実PD環の同じ(p,d)導来還元のH0は忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_reductionH0_faithfullyFlat_of_unconditional :
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) :=
    powerRootPrismMonicSourceIteratedPDResidueH0_faithfullyFlat_of_initialCoefficient W hW f
      (InitialCoefficient.sourceResidueH0_faithfullyFlat W hW f hf hdeg)
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        ((boundedAboveDerivedBaseChange q).mapIso
          (powerRootPrismMonicSourcePDSingleIso_of_unconditional W hW f hf hdeg)))).toLinearEquiv.symm

/-- 概要：実PD環の具体的A係数加群の(p,d)高次Torは零。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_torVanishing_of_unconditional : scalarExtensionTorVanishing q M := by
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
  intro n hn
  exact (powerRootPrismMonicRawPD_reduction_homology_isZero_of_unconditional W hW f hf hdeg (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso q).app M)).symm

/-- 概要：実PD環の通常係数拡大も同じ商環上忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_scalarExtension_faithfullyFlat_of_unconditional :
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) :=
    powerRootPrismMonicRawPD_reductionH0_faithfullyFlat_of_unconditional W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv.symm

/-- 概要：正次数モニック無限根族のraw実PD環は、元の(p,d)に関して完全忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_isCompletelyFaithfullyFlat_of_unconditional :
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let Mc : ModuleCat.{u} A := M
  have hFF : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    powerRootPrismMonicRawPD_scalarExtension_faithfullyFlat_of_unconditional W hW f hf hdeg
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (powerRootPrismMonicRawPD_torVanishing_of_unconditional W hW f hf hdeg) hFF.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hFF
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

/-- 概要：元の raw PD 実完備化 H の標準分母像は正則。
方針：元の実源 H⁰ の A 線形比較で生成元の単射性を移し、標準完備化射の作用を照合する。
規約：同じ H と同じ分母像を用い、hpR を仮定しない。正次数モニック入力を要求する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の H の prism 構造への無条件入力。 -/
theorem powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional :
    let := pdCompletionCommRing Raw p (c d)
    IsSMulRegular B (pdCompletionUnit Raw p (c d) (c d)) := by
  let := pdCompletionCommRing Raw p (c d)
  let := pdCompletionAlgebra Raw p (c d)
  let e := (powerRootPrismMonicSourcePDH0Iso_of_unconditional W hW f).toLinearEquiv
  have hsrc :=
    (powerRootPrismMonicSourceIteratedPDCompletion_pure_regular_of_unconditional
      W hW f hf hdeg).2.2
  have hM : Function.Injective (fun x : ModuleCat.carrier M => d • x) := by
    intro x y hxy
    apply e.symm.injective
    apply hsrc
    simpa only [← e.symm.map_smul] using congrArg e.symm hxy
  change Function.Injective (fun x : B => pdCompletionUnit Raw p (c d) (c d) * x)
  intro x y hxy
  apply hM
  change (c d) • (x : B) = (c d) • (y : B)
  have hmap : algebraMap Raw B (c d) = pdCompletionUnit Raw p (c d) (c d) :=
    pairCompletion_algebraMap Raw (p : Raw) (c d) (c d)
  simpa only [Algebra.smul_def, hmap] using hxy

end SerrePositivity.BhattScholze.Andre

end PowerRootRawPDCompletelyFlat

/-! ## 元の源の先行 p 還元と実完備化の p 正則性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の実逐次完備化を先に p で還元し、その純性を示す。

## 方針
A/(p) の被約性による d ねじれの上界と、実二生成剰余の純性・平坦性を使う。

## 規約
hpR や d mod p の正則性は要求しない。raw 環の p 正則性は結論しない。

## 使われ方
元の実完備化 H の p 正則性へ、標準 A 作用を保持して移す。
-/

@[expose] public noncomputable section PrimeReductionPurity

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

/-- 概要：被約環の任意主元の冪ねじれは、その主元で零になる。
方針：積の冪が零になることから被約性を使う。
規約：零環と冪零指数零も含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の A/(p) での有界ねじれ入力。 -/
theorem unconditionalReduced_power_torsion_bound
    {K : Type u} [CommRing K] [IsReduced K] (d : K) (n : ℕ) (x : K)
    (h : d ^ n * x = 0) : d * x = 0 := by
  apply IsNilpotent.eq_zero
  refine ⟨n + 1, ?_⟩
  calc
    (d * x) ^ (n + 1) = (d ^ n * x) * (d * x ^ n) := by
      rw [mul_pow, pow_succ, pow_succ]
      ring
    _ = 0 := by rw [h, zero_mul]

section DoubleReduction
variable {A : Type u} [CommRing A] (a b : A)
local notation "QA" => A ⧸ Ideal.span (Set.singleton a)
local notation "qA" => Ideal.Quotient.mk (Ideal.span (Set.singleton a))
local notation "QB" => QA ⧸ Ideal.span (Set.singleton (qA b))
local notation "qB" => Ideal.Quotient.mk (Ideal.span (Set.singleton (qA b)))
local notation "Q" => A ⧸ Ideal.span (Set.insert a (Set.singleton b))
local notation "q" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton b)))
local notation "e" => principalDoubleQuotEquiv a b

/-- 概要：標準二段主商の係数拡大を同じ二生成商への拡大・係数制限へ比較する。
方針：全代表元を保つ二重商同型と標準係数拡大合成を使う。
規約：a,b の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の先行 p 還元の実剰余比較。 -/
def unconditionalDoubleReductionCochainIso :
    (ModuleCat.extendScalars qA).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars qB).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.restrictScalars (e).toRingHom).mapHomologicalComplex (.up ℤ) := by
  have h : (qB).comp qA = (e).symm.toRingHom.comp q := by
    apply RingHom.ext
    intro x
    apply (e).injective
    change (e) ((qB) ((qA) x)) = (e) ((e).symm ((q) x))
    rw [RingEquiv.apply_symm_apply]
    exact principalDoubleQuotEquiv_mk a b x
  let eS : ModuleCat.extendScalars qA ⋙ ModuleCat.extendScalars qB ≅
      ModuleCat.extendScalars q ⋙ ModuleCat.restrictScalars (e).toRingHom :=
    (ModuleCat.extendScalarsComp qA qB).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars h) ≪≫
      ModuleCat.extendScalarsComp q (e).symm.toRingHom ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars q)
        (restrictScalarsIsoExtendInverse e).symm
  exact Functor.mapHomologicalComplexCompIso eS (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars q ⋙ ModuleCat.restrictScalars (e).toRingHom))
      (.up ℤ)).symm

/-- 概要：同じ二段主商比較を実導来対象に適用する。
方針：選択射影モデルと元の係数拡大モデルの比較を合成する。
規約：元の導来対象を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の先行 p 還元の純性判定。 -/
def unconditionalDoubleReductionDerivedIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange qB).obj ((boundedAboveDerivedBaseChange qA).obj X) ≅
      (boundedAboveDerivedRestrictScalars (e).toRingHom).obj
        ((boundedAboveDerivedBaseChange q).obj X) :=
  ObjectProperty.isoMk _
    (boundedAboveDerivedBaseChangeModelIso qB ((boundedAboveDerivedBaseChange qA).obj X)
        (boundedAboveDerivedBaseChangeModel qA X) ≪≫
      DerivedCategory.Q.mapIso ((unconditionalDoubleReductionCochainIso a b).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      ((derivedRestrictScalarsFactors (e).toRingHom).app
        (baseChange q (boundedAboveDerivedChosenModel X).complex)).symm ≪≫
      (derivedRestrictScalars (e).toRingHom).mapIso
        (boundedAboveDerivedBaseChangeModelIso q X (boundedAboveDerivedChosenModel X)).symm)

/-- 概要：実二段主商のホモロジーを同じ二生成商ホモロジーの係数制限へ比較する。
方針：実導来比較と正確な係数制限を合成する。
規約：全整数次数に適用する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の消滅と平坦性の移送。 -/
def unconditionalDoubleReductionHomologyIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat QB) i).obj
        ((boundedAboveDerivedBaseChange qB).obj ((boundedAboveDerivedBaseChange qA).obj X)).obj ≅
      (ModuleCat.restrictScalars (e).toRingHom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj
          ((boundedAboveDerivedBaseChange q).obj X).obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat QB) i).mapIso
      (DerivedCategory.Minus.ι.mapIso (unconditionalDoubleReductionDerivedIso a b X)) ≪≫
    (derivedRestrictScalarsHomologyIso (e).toRingHom i).app
      ((boundedAboveDerivedBaseChange q).obj X).obj

/-- 概要：二生成商の H⁰ 平坦性は実二段主商へ移る。
方針：商環同型の係数制限とホモロジー比較を使う。
規約：正則性を追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有界ねじれ純性判定への平坦性入力。 -/
theorem unconditionalDoubleReductionH0_flat
    (X : DerivedCategory.Minus (ModuleCat.{u} A))
    (h : Module.Flat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)) :
    Module.Flat QB ((DerivedCategory.homologyFunctor (ModuleCat QB) 0).obj
      ((boundedAboveDerivedBaseChange qB).obj ((boundedAboveDerivedBaseChange qA).obj X)).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
    ((boundedAboveDerivedBaseChange q).obj X).obj
  let := (e).toRingHom.toAlgebra
  let : Module QB M := Module.compHom M (e).toRingHom
  let : IsScalarTower QB Q M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : QB ≃ₐ[QB] Q := AlgEquiv.ofBijective (Algebra.ofId QB Q) (e).bijective
  have : Module.Flat QB Q := Module.Flat.of_linearEquiv eA.symm.toLinearEquiv
  have : Module.Flat Q M := h
  have : Module.Flat QB M := Module.Flat.trans QB Q M
  exact Module.Flat.of_linearEquiv (R := QB) (M := M)
    (unconditionalDoubleReductionHomologyIso a b X 0).toLinearEquiv
end DoubleReduction

/-- 概要：別の主元に関して導来完備な対象の正則主商も、商環上で導来完備。
方針：正則主商を実 Koszul 錐で計算し、係数制限で完備性を反映する。
規約：商にする元だけの正則性を要求する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の先行 p 還元の d 完備性。 -/
theorem unconditionalRegularQuotient_isComplete
    {A : Type u} [CommRing A] (a b : A) (ha : IsSMulRegular A a)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (hc : IsComplete A b X.obj) :
    IsComplete (A ⧸ Ideal.span (Set.singleton a))
      (Ideal.Quotient.mk (Ideal.span (Set.singleton a)) b)
      ((boundedAboveDerivedBaseChange
        (Ideal.Quotient.mk (Ideal.span (Set.singleton a)))).obj X).obj := by
  let q := Ideal.Quotient.mk (Ideal.span (Set.singleton a))
  let T := A ⧸ Ideal.span (Set.singleton a)
  let Y := ((boundedAboveDerivedBaseChange q).obj X).obj
  let F := derivedRestrictScalars q
  let K := DerivedCategory.Q.objPreimage X.obj
  let eK := DerivedCategory.Q.objObjPreimageIso X.obj
  have hK : IsComplete A b (DerivedCategory.Q.obj K) := isComplete_of_iso A b eK.symm hc
  have hCone := isComplete_Q_mappingCone A b (smulId a K) hK hK
  let e := restrictedDerivedQuotientKoszulIso a ha X ≪≫
    (derivedScalarConeFunctor A a).mapIso eK.symm ≪≫ (derivedScalarConeComparison A a).app K
  have hR : IsComplete A b (F.obj Y) := isComplete_of_iso A b e.symm hCone
  have hunitR : IsIso ((derivedComplexCompletionUnit A b).app (F.obj Y)) :=
    derivedComplexCompletionUnit_isIso_of_isComplete A b (F.obj Y) hR
  let eC := derivedRestrictionCompletionIso q b
  have hc' : IsIso (F.map ((derivedComplexCompletionUnit T (q b)).app Y) ≫ eC.hom.app Y) := by
    rw [derivedRestrictionCompletionIso_unit]
    exact hunitR
  have hm : IsIso (F.map ((derivedComplexCompletionUnit T (q b)).app Y)) :=
    IsIso.of_isIso_comp_right _ (eC.hom.app Y)
  have hS : IsIso ((derivedComplexCompletionUnit T (q b)).app Y) := isIso_of_reflects_iso _ F
  exact (isComplete_iff_derivedComplexCompletionUnit_isIso T (q b) Y).mpr hS

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "d" => W.generator
local notation "XC" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f
local notation "K" => A ⧸ Ideal.span {(p : A)}
local notation "qP" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "dd" => qP d
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qP) XC
local notation "Q" => A ⧸ Ideal.span {(p : A), d}
local notation "qPD" => Ideal.Quotient.mk (Ideal.span {(p : A), d})

/-- 概要：元の実逐次完備化の先行 p 還元は次数零に集中する。
方針：A/(p) の d 冪ねじれ上界、実二生成剰余の純性・平坦性、商上の d 完備性を使う。
規約：d mod p の正則性も hpR も仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の実完備化の p 正則性。 -/
theorem powerRootPrismMonicSourcePrimeReduction_pure_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    (Y).obj.IsGE 0 ∧ (Y).obj.IsLE 0 := by
  apply derived_pure_of_complete_flat_reduction dd Y
  · intro i hi
    let e := unconditionalDoubleReductionHomologyIso (p : A) d XC i
    exact ((ModuleCat.restrictScalars (principalDoubleQuotEquiv (p : A) d).toRingHom).map_isZero
      (powerRootPrismMonicSourceIteratedPDResidue_homology_isZero_of_unconditional
        W hW f hf i hi)).of_iso e
  · exact unconditionalDoubleReductionH0_flat (p : A) d XC
      (powerRootPrismMonicSourceIteratedPDResidueH0_faithfullyFlat_of_initialCoefficient W hW f
        (InitialCoefficient.sourceResidueH0_faithfullyFlat W hW f hf hdeg)).1
  · let := hW.perfectRing_mod_p
    let : IsReduced K :=
      (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr (by
        intro x hx
        exact (PerfectRing.bijective_frobenius (R := K) (p := p)).1
          (by simpa only [zero_pow (Fact.out : p.Prime).ne_zero] using hx))
    exact ⟨1, fun n x hx => by
      simpa only [pow_one] using unconditionalReduced_power_torsion_bound dd n x hx⟩
  · exact unconditionalRegularQuotient_isComplete (p : A) d hW.p_mul_injective XC
      (powerRootPrismMonicSourceIteratedPDCompletion_isComplete_d_of_unconditional W hW f)

/-- 概要：元の実逐次完備化の H⁰ で p は単射に作用する。
方針：先行 p 商の純性と元の p 導来完備性を正則商純性判定に渡す。
規約：元の A 上の実対象で述べ、raw の p 正則性は使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の H の p 正則性への移送。 -/
theorem powerRootPrismMonicSourceIteratedPDCompletion_prime_injective_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XC).obj => (p : A) • x) := by
  apply (derived_pure_of_complete_regular_quotient_pure (p : A) hW.p_mul_injective XC
    (powerRootPrismMonicSourceIteratedPDCompletion_isComplete_p_of_unconditional W hW f) ?_).2.2
  intro i hi
  obtain ⟨hGE, hLE⟩ := powerRootPrismMonicSourcePrimeReduction_pure_of_unconditional W hW f hf hdeg
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i hlt
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i hgt

local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P d
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "c" => algebraMap A Raw
local notation "H" => PDCompletionH0 Raw p (c d)
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw H)

/-- 概要：元の raw PD 実完備化 H には p ねじれがない。
方針：元の実源 H⁰ の p 単射性を標準 A 線形比較で移す。
規約：hpR・raw p 正則性を仮定せず、元の H の環構造を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化後の p 正則性の無条件版。 -/
theorem powerRootPrismMonic_pdCompletion_prime_regular_of_positive_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := pdCompletionCommRing Raw p (c d)
    IsSMulRegular H (p : H) := by
  let := pdCompletionCommRing Raw p (c d)
  let := pdCompletionAlgebra Raw p (c d)
  let e := (powerRootPrismMonicSourcePDH0Iso_of_unconditional W hW f).toLinearEquiv
  have hsrc := powerRootPrismMonicSourceIteratedPDCompletion_prime_injective_of_unconditional
    W hW f hf hdeg
  have hM : Function.Injective (fun x : ModuleCat.carrier M => (p : A) • x) := by
    intro x y hxy
    apply e.symm.injective
    apply hsrc
    simpa only [← e.symm.map_smul] using congrArg e.symm hxy
  change Function.Injective (fun x : H => (p : H) * x)
  intro x y hxy
  apply hM
  change (p : Raw) • (x : H) = (p : Raw) • (y : H)
  simpa only [Algebra.smul_def, map_natCast] using hxy

/-- 概要：次数零モニック入力では元の実完備化 H は零環。
方針：f=1 から標準分母像の乗法逆元を作り、同じ分母での導来完備性を使う。
規約：元の raw 包と元の実 H⁰ のままで述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正則性を余分な正次数仮定なしに述べる。 -/
theorem powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero
    (hf : f.Monic) (hz : f.natDegree = 0) :
    let := pdCompletionCommRing Raw p (c d)
    Subsingleton H := by
  let := pdCompletionCommRing Raw p (c d)
  have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hz
  let v := deltaAdjoinDivisionVariable E dP a (PUnit.unit : PUnit.{u + 1})
  have ha1 : a (PUnit.unit : PUnit.{u + 1}) = (1 : P) := by
    simp only [powerRootPrismMonicUnaryFamily, powerRootMonicPDInput, hf1, map_one]
  have hv : c d * v = 1 := by
    have h := deltaAdjoinDivision_relation E dP a (PUnit.unit : PUnit.{u + 1})
    rw [ha1, map_one] at h
    exact h
  let j := pdCompletionUnit Raw p (c d)
  have hvH : j (c d) * j v = 1 := by
    simpa only [map_mul, map_one] using congrArg j hv
  have hs : Function.Surjective (fun x : H => j (c d) • x) := by
    intro x
    refine ⟨j v * x, ?_⟩
    change j (c d) * (j v * x) = x
    rw [← mul_assoc, hvH, one_mul]
  have hzero := isZero_of_complete_of_smul_surjective (j (c d)) (ModuleCat.of H H)
    (pdCompletionH0_self_complete_d Raw p (c d)) hs
  change Subsingleton (ModuleCat.of H H)
  exact ModuleCat.isZero_iff_subsingleton.mp hzero

/-- 概要：元の実完備化 H は、任意のモニック入力について p 正則。
方針：正次数では先行 p 還元の純性、次数零では同じ H の零環性を使う。
規約：旧定理から hpR だけを除き、正次数仮定を追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の実 H の p 正則性の置換先。 -/
theorem powerRootPrismMonic_pdCompletion_prime_regular_of_unconditional
    (hf : f.Monic) :
    let := pdCompletionCommRing Raw p (c d)
    IsSMulRegular H (p : H) := by
  by_cases hz : f.natDegree = 0
  · let := pdCompletionCommRing Raw p (c d)
    let : Subsingleton H :=
      powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero W hW f hf hz
    change Function.Injective (fun x : H => (p : H) * x)
    intro x y _
    exact Subsingleton.elim x y
  · exact powerRootPrismMonic_pdCompletion_prime_regular_of_positive_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

/-- 概要：元の H の標準分母像は、任意のモニック入力について正則。
方針：正次数の場合の実源の純性と、次数零の場合の H の零環性を合流する。
規約：旧定理の hf を保持し、hpR と余分な正次数仮定を置かない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の H の prism 構造への入力。 -/
theorem powerRootPrismMonicRaw_pdCompletion_generator_regular_of_monic_unconditional
    (hf : f.Monic) :
    let := pdCompletionCommRing Raw p (c d)
    IsSMulRegular H (pdCompletionUnit Raw p (c d) (c d)) := by
  by_cases hz : f.natDegree = 0
  · let := pdCompletionCommRing Raw p (c d)
    let : Subsingleton H :=
      powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero W hW f hf hz
    change Function.Injective (fun x : H => pdCompletionUnit Raw p (c d) (c d) * x)
    intro x y _
    exact Subsingleton.elim x y
  · exact powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

end SerrePositivity.BhattScholze.Andre

end PrimeReductionPurity

/-! ## 元の raw 源の p 錐と d 完備化の純性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の実源の先行 p 錐を d 完備化すると負次数は消える。

## 方針
p 完備化単位の p 錐同値性と、d 完備化と p 錐の可換性を合成する。
既証明の逐次完備化の p 還元純性を、元の対象の実 d 完備化へ移す。

## 規約
元の導来源を用い、hpR・raw p 正則性・d mod p 正則性を要求しない。

## 使われ方
局所化側と組み合わせて元の raw 源の p 正則性を検出する。
-/

@[expose] public noncomputable section PowerRootRawPrimeConeCompletion

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：元の b 錐の a 完備化は、b 完備化後の a 完備化の b 錐と同型。
方針：b 完備化単位の b 錐同値と a 完備化の錐比較を合成する。
規約：a,b の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の先行 p 錐の純性。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の既証明の p 還元純性の移送。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化と完備化による raw 正則性検出。 -/
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

end PowerRootRawPrimeConeCompletion

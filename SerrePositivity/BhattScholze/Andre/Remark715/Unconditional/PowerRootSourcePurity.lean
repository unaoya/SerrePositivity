module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootSourceComplete
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.InitialCoefficient.RawResidue
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.RegularityBoundary
public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticResidue
public import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFlatReductionBounded
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity

/-!
# 元の無限根源の純性と生成元の正則性

## 概要
BS Rem 7.15（著者版 p.62）の元の実逐次完備化は次数零に集中し、生成元はその H⁰ に正則。

## 方針
A1-d の元の係数作用での忠実平坦性を受け取り、冪零還元、生成元冪商の有界 p ねじれ、
導来完備 Nakayama を順に使う。原典の p 正則基底への帰着とは異なる経路。

## 規約
hpR は仮定せず、元の源とその実完備化を使う。

## 使われ方
元の H の分母正則性と完全平坦性への作用を保つ比較に渡す。
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
使われ方：BS Rem 7.15（著者版 p.62）の冪零厚化での純性判定。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の冪零還元判定への消滅入力。 -/
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
方針：A1-d の無条件入力を実完備化へ移し、商環同型による係数制限へ移す。
規約：モニック正次数のみ追加し、別の忠実平坦性仮定を置かない。
使われ方：BS Rem 7.15（著者版 p.62）の実生成元冪商の平坦性。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商の mod p 入力。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商計算。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の実完備化の純性と分母正則性。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の元の H の分母正則性への移送。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の元の raw PD 環への比較。 -/
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

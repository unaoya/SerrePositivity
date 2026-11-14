module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.RawCompletion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.BhattScholze.Andre.Perfection.DeltaAlgebra
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfectoidization

/-!
# 完全 prism 上の根の割り算包と BS 著者版 Theorem 7.4 の別証明

## 概要
完全 prism 上の任意根族の冪商の G9 入力と離散性、源の離散性、PD 完備化環・prism 候補・perfectoid 候補の完全忠実平坦性、完全化への入力、候補の生成元商と perfectoid 商、根付き拡大と全射性、BS 著者版 Theorem 7.4 の別証明。

## 方針
André を使わない旧経路を保存したもの（2026-10-25 に主経路は原典どおり André 経由へ切り替えた）。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
BS の中には import 元がない（残した結果。`scripts/audit/bhatt_scholze.lean` が監査する）。
-/

universe u

/-! ## 完全prism上の任意根族の実冪商に対するG9標準入力 -/

@[expose] public noncomputable section PerfectPrismRootBoundedSupportPowerInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "B₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := B₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "r₀" => deltaRootRelationFamily (p := p) b
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk I₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
variable (n : ℕ) (hn : 0 < n)
local notation "X" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), d ^ n}
local notation "Yₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))) X
local notation "Tₙ" => A ⧸ Ideal.span (Set.singleton (d ^ n))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (d ^ n))))) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ))))) Zₙ
include hP hn

/-- 完全prismと任意根族の実逐次源について、G10が実冪剰余の純粋性とH0忠実平坦性を与える。 -/
theorem perfectPrismRootBoundedSupportPower_pure_faithfullyFlat
    (hpres : ∀ i : ℕ, PreservesColimit
  (deltaDivisionBoundedSupportModuleDiagram E₀ r₀)
  ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    (Yₙ).obj.IsGE 0 ∧ (Yₙ).obj.IsLE 0 ∧
      Module.FaithfullyFlat Qₙ
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  exact prismaticPowerDerivedReduction_pure_faithfullyFlat (p : A) d n hn X
    (deltaRootBoundedSupportIteratedPDResidue_homology_isZero D d b hP.p_mul_injective
      P.generator_regular v hv hpres)
    (deltaRootBoundedSupportIteratedPDResidueH0_faithfullyFlat D d b hP.p_mul_injective
      P.generator_regular v hv hpres)

/-- 同じ生成元冪商上の標準mod p実還元は、次数零集中・H0平坦。 -/
theorem perfectPrismRootBoundedSupportPower_modP_inputs
    (hpres : ∀ i : ℕ, PreservesColimit
  (deltaDivisionBoundedSupportModuleDiagram E₀ r₀)
  ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    (∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  obtain ⟨hGE, hLE, hFF⟩ :=
    perfectPrismRootBoundedSupportPower_pure_faithfullyFlat P hP b n hn hpres
  refine ⟨?_, prismaticGeneratorPowerModPH0_flat p d n X hFF.1⟩
  intro i hi
  apply prismaticGeneratorPowerModP_homology_isZero p d n X i
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 同じ具体的実冪商に、G9の完備性・係数ねじれ上界・標準mod p純粋平坦性を供給する。 -/
theorem perfectPrismRootBoundedSupportPower_G9_inputs
    (hpres : ∀ i : ℕ, PreservesColimit
  (deltaDivisionBoundedSupportModuleDiagram E₀ r₀)
  ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ k : ℕ, ∀ x : Tₙ, (p : Tₙ) ^ k * x = 0 → (p : Tₙ) ^ n * x = 0) ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  obtain ⟨hz, hflat⟩ := perfectPrismRootBoundedSupportPower_modP_inputs P hP b n hn hpres
  refine ⟨deltaRootSourceGeneratorPowerReduction_isComplete_over_quotient
    D d b P.generator_regular n, ?_, hz, hflat⟩
  let := P.isAdicComplete_p_of_perfect hP
  intro k x hx
  exact hP.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
    (P.isDistinguished_generator) n k x hx

/-- G9-4の同じ選択モデルのp余核複体にも、標準実還元の非零次数消滅を渡す。 -/
theorem perfectPrismRootBoundedSupportPower_modP_cokernel_homology_isZero
    (hpres : ∀ i : ℕ, PreservesColimit
  (deltaDivisionBoundedSupportModuleDiagram E₀ r₀)
  ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCompletion.powerCokernelComplex (p : Tₙ)
      (boundedAboveDerivedChosenModel Zₙ).complex 1).homology i) := by
  apply DerivedCompletion.powerCokernel_homology_isZero_of_reduction (p : Tₙ) 1 Zₙ i
  let H (a : Tₙ) := IsZero
    ((DerivedCategory.homologyFunctor (ModuleCat (Tₙ ⧸ Ideal.span {a})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj Zₙ).obj)
  have hz : H (p : Tₙ) :=
    (perfectPrismRootBoundedSupportPower_modP_inputs P hP b n hn hpres).1 i hi
  exact Eq.mp (congrArg H (_root_.pow_one (p : Tₙ)).symm) hz

end SerrePositivity.BhattScholze

end PerfectPrismRootBoundedSupportPowerInputs

/-! ## 完全prism上の任意根族の実生成元冪商の離散性 -/

@[expose] public noncomputable section PerfectPrismRootPowerDiscrete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "B₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := B₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "r₀" => deltaRootRelationFamily (p := p) b
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk I₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
variable (n : ℕ) (hn : 0 < n)
local notation "X" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), d ^ n}
local notation "Yₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))) X
local notation "Tₙ" => A ⧸ Ideal.span (Set.singleton (d ^ n))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (d ^ n))))) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ))))) Zₙ
include hP hn

/-- 元の実逐次源の生成元冪商は離散で、そのH0は有界p冪ねじれを持つ。 -/
theorem perfectPrismRootPower_pure_bounded_torsion :
    (Zₙ).obj.IsGE 0 ∧ (Zₙ).obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ z : (DerivedCategory.homologyFunctor (ModuleCat.{u} Tₙ) 0).obj (Zₙ).obj,
          (p : Tₙ) ^ k • z = 0 → (p : Tₙ) ^ N • z = 0 := by
  obtain ⟨hc, ht, hz, hf⟩ := perfectPrismRootBoundedSupportPower_G9_inputs P hP b n hn
    (deltaRootBoundedSupport_preservesColimit D d b)
  exact DerivedCompletion.derived_pure_bounded_torsion_of_complete_flat_reduction
    (p : Tₙ) Zₙ hz hf ⟨n, ht⟩ hc

/-- 同じ具体的実冪商の非零次数のホモロジーは零。 -/
theorem perfectPrismRootPower_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Tₙ) i).obj (Zₙ).obj) := by
  obtain ⟨hGE, hLE, _⟩ := perfectPrismRootPower_pure_bounded_torsion P hP b n hn
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

end SerrePositivity.BhattScholze

end PerfectPrismRootPowerDiscrete

/-! ## 完全prism上の任意根族の元の実逐次源の離散性 -/

@[expose] public noncomputable section PerfectPrismRootSourceDiscrete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "X" => DeltaRootSourceIteratedPDCompletion D d b
include hP

/-- 同じ元の実逐次源の生成元冪余核は、零冪も含め全負次数で消える。 -/
theorem perfectPrismRootSource_powerCokernel_homology_isZero
    (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((powerCokernelComplex d (boundedAboveDerivedChosenModel X).complex n).homology i) := by
  apply powerCokernel_homology_isZero_of_reduction d n X i
  by_cases hn : 0 < n
  · exact perfectPrismRootPower_homology_isZero P hP b n hn i (by omega)
  · have hn0 : n = 0 := by omega
    subst n
    let : Subsingleton (A ⧸ Ideal.span {d ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact Module.subsingleton (A ⧸ Ideal.span {d ^ 0}) _

/-- 完全prism上の任意根族の元の実p,d逐次完備化源は離散。 -/
theorem perfectPrismRootSource_pure :
    (X).obj.IsGE 0 ∧ (X).obj.IsLE 0 := by
  have hmod (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {d})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj X).obj) := by
    let F (t : A) := IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {t})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {t}))).obj X).obj)
    exact Eq.mp (congrArg F (pow_one d))
      (perfectPrismRootPower_homology_isZero P hP b 1 (by omega) i hi)
  obtain ⟨hGE, hLE, _⟩ := derived_pure_of_complete_regular_quotient_pure d
    P.generator_regular X (deltaRootSourceIteratedPDCompletion_isComplete_d D d b) hmod
  exact ⟨hGE, hLE⟩

/-- 元の実逐次源の非零次数ホモロジーは全て消える。 -/
theorem perfectPrismRootSource_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismRootSource_pure P hP b
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 離散性により、元の実逐次源をその実H0のsingle対象と同定する。 -/
def perfectPrismRootSourceSingleIso :
    (X).obj ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismRootSource_pure P hP b
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso (X).obj 0

/-- このsingle比較は同じ実H0上で恒等写像に正規化されている。 -/
theorem perfectPrismRootSourceSingleIso_homologyZero :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (perfectPrismRootSourceSingleIso P hP b).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).hom.app
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (X).obj) = 𝟙 _ := by
  obtain ⟨hGE, hLE⟩ := perfectPrismRootSource_pure P hP b
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso_homology (X).obj 0

end SerrePositivity.BhattScholze

end PerfectPrismRootSourceDiscrete

/-! ## 完全prism上の任意根族の実PD完備化環の完全忠実平坦性 -/

@[expose] public noncomputable section PerfectPrismRootPDCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "B" => PDCompletionH0 Raw p (c d)
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "X" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (boundedAboveDerivedSingleFunctor.obj M)
include hP

/-- 元の実逐次源は、標準A作用付きraw PD環のsingle対象と同型。 -/
def perfectPrismRootSourcePDSingleIso : X ≅ boundedAboveDerivedSingleFunctor.obj M :=
  ObjectProperty.isoMk _ (perfectPrismRootSourceSingleIso P hP b ≪≫
    (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso (deltaRootSourcePDH0Iso D d b))

/-- 実PD環の同じ(p,d)導来還元の非零次数は消える。 -/
theorem perfectPrismRootPD_reduction_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  have hz := deltaRootBoundedSupportIteratedPDResidue_homology_isZero D d b
    hP.p_mul_injective P.generator_regular v hv
    (deltaRootBoundedSupport_preservesColimit D d b) i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      ((boundedAboveDerivedBaseChange q).mapIso (perfectPrismRootSourcePDSingleIso P hP b)))).symm

/-- 実PD環の同じ(p,d)導来還元のH0は忠実平坦。 -/
theorem perfectPrismRootPD_reductionH0_faithfullyFlat :
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) :=
    deltaRootBoundedSupportIteratedPDResidueH0_faithfullyFlat D d b
    hP.p_mul_injective P.generator_regular v hv
    (deltaRootBoundedSupport_preservesColimit D d b)
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        ((boundedAboveDerivedBaseChange q).mapIso
          (perfectPrismRootSourcePDSingleIso P hP b)))).toLinearEquiv.symm

/-- 実PD環の具体的A係数加群の(p,d)高次Torは零。 -/
theorem perfectPrismRootPD_torVanishing : scalarExtensionTorVanishing q M := by
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
  intro n hn
  exact (perfectPrismRootPD_reduction_homology_isZero P hP b (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso q).app M)).symm

/-- 実PD環の通常係数拡大も同じ商環上忠実平坦。 -/
theorem perfectPrismRootPD_scalarExtension_faithfullyFlat :
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) :=
    perfectPrismRootPD_reductionH0_faithfullyFlat P hP b
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv.symm

/-- 任意根族のraw実PD環は、元の(p,d)に関して完全忠実平坦。 -/
theorem perfectPrismRootPD_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let Mc : ModuleCat.{u} A := M
  have hFF : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    perfectPrismRootPD_scalarExtension_faithfullyFlat P hP b
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (perfectPrismRootPD_torVanishing P hP b) hFF.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hFF
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

end SerrePositivity.BhattScholze

end PerfectPrismRootPDCompletelyFlat

/-! ## 任意根族の実PD環から実δ完全化の離散性への具体的入力 -/

@[expose] public noncomputable section PerfectPrismRootPDPerfectionInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
section Coefficients
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor (baseChangeScalarModule j))

/-- 実PD係数加群は、元の標準環射A→PDに沿う制限加群そのものである。 -/
def deltaRootPDSourceModuleIso :
    letI := pdCompletionCommRing Raw p z
    M ≅ baseChangeScalarModule j := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionAlgebra Raw p z
  let Mc : ModuleCat.{u} A := M
  let Nc : ModuleCat.{u} A := baseChangeScalarModule j
  let f : Mc →ₗ[A] Nc :=
    { toFun := (id : B → B)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change B at x
        change (c a) • x = s (c a) * x
        exact Algebra.smul_def (c a) x }
  let g : Nc →ₗ[A] Mc :=
    { toFun := (id : B → B)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change B at x
        change s (c a) * x = (c a) • x
        exact (Algebra.smul_def (c a) x).symm }
  let e : Mc ≃ₗ[A] Nc := LinearEquiv.ofLinearMap f g (by ext x; rfl) (by ext x; rfl)
  exact e.toModuleIso

/-- 同じ標準PD係数射は、元のδ構造からのδ射。 -/
theorem deltaRootPDSourceCoefficient_isDeltaHom :
    letI := pdCompletionCommRing Raw p z
    D.IsDeltaHom G j := by
  let := pdCompletionCommRing Raw p z
  exact (pdCompletionUnit_isDeltaHom F z).comp
    ((deltaAdjoinDivisionMap_isDeltaHom E (MvPolynomial.C d) r).comp
      (polynomialRankOneDeltaStructure_C_isDeltaHom σ D))

end Coefficients

section Perfect
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor (baseChangeScalarModule j))

include hP

/-- 完全prism上では、同じPD係数射に沿う実還元の非零次数は消える。 -/
theorem perfectPrismRootPDSource_reduction_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := pdCompletionCommRing Raw p z
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  have hz := perfectPrismRootPD_reduction_homology_isZero P hP b i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
      (boundedAboveDerivedSingleFunctor.mapIso (deltaRootPDSourceModuleIso D d b))))).symm

/-- 同じ標準PD係数射に沿う実還元のH0は忠実平坦。 -/
theorem perfectPrismRootPDSource_reductionH0_faithfullyFlat :
    letI := pdCompletionCommRing Raw p z
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  let : Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj) :=
    perfectPrismRootPD_reductionH0_faithfullyFlat P hP b
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
        (boundedAboveDerivedSingleFunctor.mapIso
          (deltaRootPDSourceModuleIso D d b))))).toLinearEquiv.symm

/-- 任意根族の実PD環のδ完全化を逐次実完備化した具体的対象は離散。 -/
theorem perfectPrismRootPDPerfectionCompletion_pure :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletion_pure P G j hP
    (deltaRootPDSourceCoefficient_isDeltaHom D d b)
    (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
    (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b)

/-- 同じ具体的δ完全化逐次対象の生成元冪商も離散でH0のp冪ねじれは有界。 -/
theorem perfectPrismRootPDPerfectionPower_pure_bounded_torsion (n : ℕ) (hn : 0 < n) :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    let T := A ⧸ Ideal.span {d ^ n}
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) 0).obj Z.obj,
          (p : T) ^ k • x = 0 → (p : T) ^ N • x = 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion P G j hP
    (deltaRootPDSourceCoefficient_isDeltaHom D d b)
    (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
    (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b) n hn

end Perfect
end SerrePositivity.BhattScholze

end PerfectPrismRootPDPerfectionInputs

/-! ## 既存根prism台環候補の標準係数射の完全忠実平坦性 -/

@[expose] public noncomputable section PerfectPrismRootPrismCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
section Coefficients
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "H" => PDCompletionH0 C p (κ d)
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "T" => DeltaRootPrismCarrier D d b
local notation "f" => deltaRootPrismCoefficientMap D d b

/-- 既存の標準環同型は、両候補の元のA係数作用を保つ線形同型。 -/
def deltaRootPDPerfectionCandidateModuleIso :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p (κ d)
    letI := deltaRootPrismCommRing D d b
    baseChangeScalarModule t ≅ baseChangeScalarModule f := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := deltaRootPrismCommRing D d b
  let e : H ≃+* T := deltaRootPDCompletedPerfectionEquiv D d b
  let Mc : ModuleCat.{u} A := baseChangeScalarModule t
  let Nc : ModuleCat.{u} A := baseChangeScalarModule f
  let eA : Mc ≃ₗ[A] Nc :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        change H at x
        change e (t a * x) = f a * e x
        rw [map_mul]
        exact congrArg (fun h => h * e x)
          (RingHom.congr_fun (deltaRootPDCompletedPerfectionEquiv_comp_coefficient D d b) a) }
  exact eA.toModuleIso
end Coefficients

section Perfect
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "f" => deltaRootPrismCoefficientMap D d b
local notation "M" => baseChangeScalarModule f
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
include hP

/-- 実根PD環をδ完全化して実PD完備化した環の標準A作用は完全忠実平坦。 -/
theorem perfectPrismRootPDPerfection_isCompletelyFaithfullyFlat :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p (κ d)
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier (baseChangeScalarModule t)) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  exact perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat P G j hP
    (deltaRootPDSourceCoefficient_isDeltaHom D d b)
    (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
    (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b)

/-- 既存根prism台環の元の係数射は(p,d)残余Tor非輪状。 -/
theorem perfectPrismRootPrism_torVanishing :
    letI := deltaRootPrismCommRing D d b
    scalarExtensionTorVanishing q M := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := deltaRootPrismCommRing D d b
  exact scalarExtensionTorVanishing_of_iso q (deltaRootPDPerfectionCandidateModuleIso D d b)
    (perfectPrismDeltaAlgebraPD_torVanishing P G j hP
      (deltaRootPDSourceCoefficient_isDeltaHom D d b)
      (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
      (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b))

/-- 同じ既存候補の通常残余係数拡大は忠実平坦。 -/
theorem perfectPrismRootPrism_scalarExtension_faithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := deltaRootPrismCommRing D d b
  let M0 : ModuleCat.{u} A := baseChangeScalarModule t
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M0) :=
    perfectPrismDeltaAlgebraPD_scalarExtension_faithfullyFlat P G j hP
      (deltaRootPDSourceCoefficient_isDeltaHom D d b)
      (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
      (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b)
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q).obj M0)
    (((ModuleCat.extendScalars q).mapIso
      (deltaRootPDPerfectionCandidateModuleIso D d b)).toLinearEquiv.symm)

/-- 任意根族の既存根prism台環候補は、その標準係数射に関して(p,d)完全忠実平坦。 -/
theorem perfectPrismRootPrism_isCompletelyFaithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let := deltaRootPrismCommRing D d b
  let Mc : ModuleCat.{u} A := M
  have hf : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    perfectPrismRootPrism_scalarExtension_faithfullyFlat P hP b
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (perfectPrismRootPrism_torVanishing P hP b) hf.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hf
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm
end Perfect
end SerrePositivity.BhattScholze

end PerfectPrismRootPrismCompletelyFlat

/-! ## 根prism候補の実生成元商と標準perfectoid商の同定 -/

@[expose] public noncomputable section PerfectPrismRootQuotientReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_generator P
local notation "T" => DeltaRootPrismCarrier D d b
local notation "f" => deltaRootPrismCoefficientMap D d b
local notation "J" => Ideal.span {d}
local notation "R" => A ⧸ J
local notation "q" => Ideal.Quotient.mk J
local notation "P'" => deltaRootPrism D d b hd
local notation "S" => DeltaRootPerfectoidCandidate D d b hd
local notation "g" => deltaRootPerfectoidCandidateBaseMap D d b hd
local notation "M" => baseChangeScalarModule f
include hP

/-- 候補の生成元の正則性は、元Aのdによるスカラー作用の正則性でもある。 -/
theorem perfectPrismRootPrism_generator_smul_regular :
    letI := deltaRootPrismCommRing D d b
    IsSMulRegular (ModuleCat.carrier M) d := by
  let := deltaRootPrismCommRing D d b
  intro x y h
  change T at x y
  change f d * x = f d * y at h
  exact (P').generator_regular h

/-- 元と候補の生成元が正則なので、生成元商への実係数拡大はTor非輪状。 -/
theorem perfectPrismRootPrism_generator_torVanishing :
    letI := deltaRootPrismCommRing D d b
    scalarExtensionTorVanishing q M := by
  let := deltaRootPrismCommRing D d b
  exact scalarExtensionTorVanishing_principal_of_regular d P.generator_regular M
    (perfectPrismRootPrism_generator_smul_regular P hP b)

/-- 通常生成元商の標準係数作用を既存perfectoid候補の基底射と照合する。 -/
def perfectPrismRootPrism_ordinaryQuotientIso :
    letI := deltaRootPrismCommRing D d b
    (ModuleCat.extendScalars q).obj M ≅ baseChangeScalarModule g := by
  let := deltaRootPrismCommRing D d b
  let := deltaRootPrismCoefficientAlgebra D d b
  have hI : (J).map (algebraMap A T) = (P').ideal := by
    change (J).map f = (P').ideal
    exact deltaRootPrismCoefficientMap_ideal D d b hd
  let eR : (T ⧸ (J).map (algebraMap A T)) ≃+* S := Ideal.quotEquivOfEq hI
  let Mc : ModuleCat.{u} R := ModuleCat.of R (T ⧸ (J).map (algebraMap A T))
  let Nc : ModuleCat.{u} R := baseChangeScalarModule g
  let eA : Mc ≃ₗ[R] Nc :=
    { eR.toAddEquiv with
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change eR (Ideal.Quotient.mk _ (f a) * x) =
          Ideal.Quotient.mk (P').ideal (f a) * eR x
        rw [map_mul]
        rfl }
  exact (ModuleCat.extendScalars q).mapIso (algebraSelfRestrictionIso A T) ≪≫
    (quotientAlgebraScalarExtensionEquiv J T).toModuleIso ≪≫ eA.toModuleIso

/-- 元の実生成元還元は、既存perfectoid商の同じ基底射付きsingle対象と同型。 -/
def perfectPrismRootPrism_derivedQuotientIso :
    letI := deltaRootPrismCommRing D d b
    (boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule g) := by
  let := deltaRootPrismCommRing D d b
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso q M
    (perfectPrismRootPrism_generator_torVanishing P hP b) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso (perfectPrismRootPrism_ordinaryQuotientIso P b)

end SerrePositivity.BhattScholze

end PerfectPrismRootQuotientReduction

/-! ## 任意根族のperfectoid候補の標準基底射のp完全忠実平坦性 -/

@[expose] public noncomputable section PerfectPrismRootPerfectoidCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_generator P
local notation "f" => deltaRootPrismCoefficientMap D d b
local notation "M" => baseChangeScalarModule f
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M
local notation "J" => Ideal.span {d}
local notation "R" => A ⧸ J
local notation "q" => Ideal.Quotient.mk J
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q₀" => Ideal.Quotient.mk I
local notation "g" => deltaRootPerfectoidCandidateBaseMap D d b hd
local notation "N" => baseChangeScalarModule g
local notation "K" => Ideal.span {(p : R)}
local notation "Qp" => R ⧸ K
local notation "qp" => Ideal.Quotient.mk K
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qp)
  (Functor.obj boundedAboveDerivedSingleFunctor N)
include hP

/-- 既存根prismの同じ(p,d)実還元の非零次数は消える。 -/
theorem perfectPrismRootPrism_pair_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := deltaRootPrismCommRing D d b
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := deltaRootPrismCommRing D d b
  let e := boundedAboveDerivedBaseChangeModuleAugmentationIso q₀ M
    (perfectPrismRootPrism_torVanishing P hP b)
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q₀).obj M) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e))

/-- 同じ根prismの実(p,d)還元のH0は忠実平坦。 -/
theorem perfectPrismRootPrism_pairH0_faithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := deltaRootPrismCommRing D d b
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q₀).obj M) :=
    perfectPrismRootPrism_scalarExtension_faithfullyFlat P hP b
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q₀).obj M)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q₀).app M).toLinearEquiv

/-- perfectoid商の標準基底射の実mod p還元の非零次数は消える。 -/
theorem perfectPrismRootPerfectoid_modP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := deltaRootPrismCommRing D d b
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj (Y).obj) := by
  let := deltaRootPrismCommRing D d b
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj
      ((boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)).obj) := by
    let HQ (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismRootPrism_pair_homology_isZero P hP b i hi
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModP_homology_isZero p d 1 X i hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
      (perfectPrismRootPrism_derivedQuotientIso P hP b)))).symm

/-- 同じ実mod p還元のH0は、正確な基底剰余環上で忠実平坦。 -/
theorem perfectPrismRootPerfectoid_modPH0_faithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    Module.FaithfullyFlat Qp ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) := by
  let := deltaRootPrismCommRing D d b
  let W := (boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj) := by
    let HQ (a : A) := Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), a})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismRootPrism_pairH0_faithfullyFlat P hP b
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := Module.FaithfullyFlat
      ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})
      ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModPH0_faithfullyFlat p d 1 X hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
        (perfectPrismRootPrism_derivedQuotientIso P hP b)))).toLinearEquiv.symm

/-- 同じperfectoid商の基底係数加群の高次mod p Torは零。 -/
theorem perfectPrismRootPerfectoid_torVanishing :
    letI := deltaRootPrismCommRing D d b
    scalarExtensionTorVanishing qp N := by
  let := deltaRootPrismCommRing D d b
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff qp N).mp
  intro n hn
  exact (perfectPrismRootPerfectoid_modP_homology_isZero P hP b (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso qp).app N)).symm

/-- 同じperfectoid商の通常mod p係数拡大は忠実平坦。 -/
theorem perfectPrismRootPerfectoid_scalarExtension_faithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj N) := by
  let := deltaRootPrismCommRing D d b
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) :=
    perfectPrismRootPerfectoid_modPH0_faithfullyFlat P hP b
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso qp).app N).toLinearEquiv.symm

/-- 任意根族のperfectoid候補の標準基底射はp完全忠実平坦。 -/
theorem perfectPrismRootPerfectoid_isCompletelyFaithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    IsCompletelyFaithfullyFlat K (ModuleCat.carrier N) := by
  let := deltaRootPrismCommRing D d b
  let Nc : ModuleCat.{u} R := N
  have hf : Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj Nc) :=
    perfectPrismRootPerfectoid_scalarExtension_faithfullyFlat P hP b
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction K Nc
    (perfectPrismRootPerfectoid_torVanishing P hP b) hf.1, ?_⟩
  let e := (quotientScalarExtensionEquiv K Nc).trans (quotientTensorReductionEquiv K Nc).symm
  let := hf
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

end SerrePositivity.BhattScholze

end PerfectPrismRootPerfectoidCompletelyFlat

/-! ## 完全prism商の根付きp完全忠実平坦perfectoid拡大と全射性 -/

@[expose] public noncomputable section PerfectPrismRootedPerfectoidExtension

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_generator P
local notation "R" => A ⧸ Ideal.span {d}
include hP

/-- 候補商の通常の基底代数作用も、元の標準射に関してp完全忠実平坦。 -/
theorem perfectPrismRootPerfectoid_baseAlgebra_isCompletelyFaithfullyFlat (b : σ → A) :
    letI := deltaRootPrismCommRing D d b
    letI := (deltaRootPerfectoidCandidateBaseMap D d b hd).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) (DeltaRootPerfectoidCandidate D d b hd) := by
  let := deltaRootPrismCommRing D d b
  let T := DeltaRootPerfectoidCandidate D d b hd
  let g := deltaRootPerfectoidCandidateBaseMap D d b hd
  let := g.toAlgebra
  let I := Ideal.span {(p : R)}
  let q := Ideal.Quotient.mk I
  let M0 : ModuleCat.{u} R := baseChangeScalarModule g
  let M1 := ModuleCat.of R T
  let e : M0 ≅ M1 := algebraSelfRestrictionIso R T
  have ht : scalarExtensionTorVanishing q M1 := scalarExtensionTorVanishing_of_iso q e
    (perfectPrismRootPerfectoid_torVanishing P hP b)
  let : Module.FaithfullyFlat (R ⧸ I) ((ModuleCat.extendScalars q).obj M0) :=
    perfectPrismRootPerfectoid_scalarExtension_faithfullyFlat P hP b
  have hf : Module.FaithfullyFlat (R ⧸ I) ((ModuleCat.extendScalars q).obj M1) :=
    Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) ((ModuleCat.extendScalars q).obj M0)
      (((ModuleCat.extendScalars q).mapIso e).toLinearEquiv.symm)
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I T ht hf.1, ?_⟩
  let eTensor := (quotientScalarExtensionEquiv I M1).trans (quotientTensorReductionEquiv I T).symm
  let := hf
  exact Module.FaithfullyFlat.of_linearEquiv _ _ eTensor.symm

/-- 完全prism商の任意の元族に、具体的なp完全忠実平坦perfectoid拡大と互換根を供給する。 -/
theorem exists_rootedPerfectoidExtension_of_perfectPrism (a : σ → R) :
    ∃ (T : Type u) (_ : CommRing T) (f : R →+* T) (ρ : σ → ℕ → T),
      IsIntegralPerfectoid T p ∧
      (letI := f.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      (∀ s, ρ s 0 = f (a s)) ∧ (∀ s n, ρ s (n + 1) ^ p = ρ s n) := by
  let b : σ → A := fun s => Classical.choose (Ideal.Quotient.mk_surjective (a s))
  have hb (s : σ) : Ideal.Quotient.mk (Ideal.span {d}) (b s) = a s :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (a s))
  let := deltaRootPrismCommRing D d b
  refine ⟨DeltaRootPerfectoidCandidate D d b hd, inferInstance,
    deltaRootPerfectoidCandidateBaseMap D d b hd,
    deltaRootPerfectoidCandidateRoots D d b hd,
    deltaRootPerfectoidCandidate_isIntegralPerfectoid D d b hd,
    perfectPrismRootPerfectoid_baseAlgebra_isCompletelyFaithfullyFlat P hP b, ?_, ?_⟩
  · intro s
    rw [deltaRootPerfectoidCandidateRoots_zero, hb]
  · exact deltaRootPerfectoidCandidateRoots_pow D d b hd

/-- 完全prism商の導来p完備な全射商では、任意の普遍perfectoid化は全射。 -/
theorem surjective_of_isPerfectoidization_of_perfectPrism_quotient
    {S C : Type u} [CommRing S] [CommRing C]
    (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  obtain ⟨T, hT, g, ρ, hperf, hflat, hρ0, hρ⟩ :=
    exists_rootedPerfectoidExtension_of_perfectPrism P hP (fun s : RingHom.ker q => (s : R))
  let := hT
  let := g.toAlgebra
  have hR : IsIntegralPerfectoid R p := P.quotient_isIntegralPerfectoid hP
  exact surjective_of_isPerfectoidization_of_sourceKernelRoots
    hR hperf q hq hS hflat ρ hρ0 hρ f hf

end SerrePositivity.BhattScholze

end PerfectPrismRootedPerfectoidExtension

/-! ## 根の割り算包による別証明

## 概要
perfectoid 環の導来 p 完備な全射商の任意の perfectoid 化は全射（BS 著者版 Theorem 7.4）の、
André の補題を使わない別証明。

## 方針
完全 prism 上で核の元に両立する p 冪根を添加する割り算包を作り、その完備化が
p 完全忠実平坦な perfectoid 拡大になることを示して降下する。

## 規約
主張は B4 と同じ。B4 本体は原典どおり André 経由
（`Semiperfectoid/SemiperfectoidSurjectivity`）。

## 使われ方
主定理の経路では使わない。完全 prism 上の \(X^p-b\) 族の prismatic envelope の計算
（A3 の候補）とともに保存する。
-/

@[expose] public noncomputable section RootEnvelopeSurjectivity

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S C : Type u}
variable [CommRing R] [CommRing S] [CommRing C]

/-- 任意perfectoid環の導来p完備な全射商の、任意の普遍perfectoid化は全射（BS 著者版 Theorem 7.4 の根の包を経由する証明）。
André の補題を使わず、完全 prism 上の根の割り算包から降下する別証明。 -/
theorem surjective_of_isPerfectoidization_of_semiperfectoid_quotient_of_rootEnvelope
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  rcases hR with hs | ⟨hp, hc, ⟨π, u, hu⟩, hF, hker⟩
  · let := hs
    let : Subsingleton S := q.codomain_trivial
    let : Subsingleton C := f.codomain_trivial
    exact fun y => ⟨0, Subsingleton.elim _ _⟩
  · let := hc
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    obtain ⟨d, hd, e, _⟩ := exists_perfectoidTrialPrism R p hF hker π u hu
    let := DerivedCompletion.pdCompletionCommRing (WittVector p (PreTilt R p)) p d
    let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    have hP := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    exact surjective_of_isPerfectoidization_of_perfectPrism_quotient P hP
      (q.comp e.toRingHom) (hq.comp e.surjective) hS f hf

end SerrePositivity.BhattScholze

end RootEnvelopeSurjectivity

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 7.4"] _root_.SerrePositivity.BhattScholze.surjective_of_isPerfectoidization_of_semiperfectoid_quotient_of_rootEnvelope

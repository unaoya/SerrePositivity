module

public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.BhattScholze.Perfectoidization.FiniteComparisonExcision
public import SerrePositivity.BhattScholze.Perfectoidization.Excision
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import SerrePositivity.CommutativeAlgebra.RootTower.BaseChange
public import SerrePositivity.HomologicalAlgebra.Koszul.ParameterAnnihilators
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.BaseChange
public import SerrePositivity.HomologicalAlgebra.TorFiniteCoefficients
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorAlgebraComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IdealExtension
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.CLMST.Algebra
public import SerrePositivity.BhattScholze.PerfectoidIdeal.CompletedQuotient
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.HomologicalAlgebra.PowerTorsionTorBaseChange
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.Actions
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite

/-! # Cor 4.0.4：perfectoid イデアルによる局所コホモロジーと Koszul ホモロジーの零化

## 概要

固定した `g` の外で有限エタールなら、低次の局所コホモロジーと全ての有限段の任意のパラメータ系の正の次数の Koszul ホモロジーが perfectoid イデアルで零化される（`corollary_4_0_4`）。条件つきの形（`conditional_corollary_4_0_4`）、有限段の Koszul の零化、選んだ `RPerfd` の上の比較の入力、完備塔の Tor の検査から係数の入力を得ること、Prop 2.4.9(a)（`perfectoidIdeal_powerTorsionTorInput`）、有限エタールな開集合の存在（`exists_finite_etale_away`）、パラメータ系の消滅への接続（`exists_perfectoidIdeal_annihilates_koszul`）を与える。

## 方針

有限比較の excision（BhattScholze/Perfectoidization/FiniteComparisonExcision）を供給し、塔の側の冪ねじれ Tor の入力を KL-Q に渡す。`A` への平坦な基底変更と全加群版への移送を使う。

## 規約

CLMST Cor 4.0.4（p.28）・Prop 2.4.9(a)・Notation 4.0.1。旧入口 `Inputs.corollary_4_0_4` は同じ主張の重複なので削除した。旧 `CLMST/EtaleLocus`・`KLFiniteComparisonExcision`・`ConditionalCohomologyVanishing`・`FiniteStageKoszulAnnihilator`・`RPerfdCohomologyInputs`・`RPerfdTorBaseChange`・`KLCohomologyFromExcision`・`Corollary404`・`CohomologyVanishing`・`Inputs/CohomologyVanishing`。

## 使われ方

Paper（Theorem 2.5 の混標数、`MixedChar`）、`CyclicLengthBound`、`ParameterQuotientLength`。
-/

@[expose] public noncomputable section

universe u

section EtaleLocusPart

namespace SerrePositivity.CLMST

/-- CLMST で用いる有限拡大は、基底環のある非零元の反転後に有限エタールとなる。
局所化間の作用は元の代数写像を局所化した標準の awayAlgebra である。 -/
theorem exists_finite_etale_away (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsDomain D] [CharZero D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D)) :
    ∃ g : A, g ≠ 0 ∧
      let _ := GenericEtale.awayAlgebra A D g
      Module.Finite (Localization.Away g) (Localization.Away (algebraMap A D g)) ∧
        Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)) := by
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  exact GenericEtale.exists_finite_etale_away_of_charZero A D hinj

end SerrePositivity.CLMST

end EtaleLocusPart

section KLFiniteComparisonExcisionPart

namespace SerrePositivity.CLMST
open _root_.SerrePositivity.BhattScholze _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false

/--
## 概要
有限表示な有限代数が a の外でエタールなら、元の perfectoid ideal の全元は
任意の p 冪ねじれ試験加群に対する正次数 Tor の元の係数作用を零化する。

## 方針
一つの André 拡大上で有限比較 excision を供給し、既存の忠実な Tor 検出で元の基底へ戻す。
拡大と比較モデルの選択は、全試験加群・全指数・全正次数に先行する。

## 使われ方
Prop 2.4.9(a) の入力 (a) として KL の全加群版とコホモロジー消滅に用いる。
-/
theorem perfectoidIdeal_powerTorsionTorInput
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (a : R) (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    letI := GenericEtale.awayAlgebra R A a
    Algebra.Etale (Localization.Away a) (Localization.Away (algebraMap R A a)) →
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
        ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
          torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  exact BhattScholze.perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision p hR
    (fun E _ _ hE _ => BhattScholze.klFiniteComparisonExcision_of_perfectoid E p hE) a f hf

end SerrePositivity.CLMST

end KLFiniteComparisonExcisionPart

section FiniteStageKoszulAnnihilatorPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.Section2

/-- The actual finite stages provide all the parameter support hypotheses for KL4/KL5. -/
lemma finiteStageKoszul_positive_annihilator
    {A D C S : Type u} [CommRing A] [IsNoetherianRing A] [CommRing D] [IsLocalRing D]
    [CommRing C] [CommRing S] [Algebra A D] [Module.Finite A D] [Algebra A C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (hres : ∀ k : ℕ, IsKoszulResolution (fun j => t j ^ k))
    (n : ℕ) (φ : Section2.StageAlgebra A D t p n →+* C)
    (hφ : ∀ x : A, φ (algebraMap D (Section2.StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (ψ : S →+* C) (I : Ideal S) (a : S) (j₀ : Fin e)
    (ha : ψ a = algebraMap A C (t j₀))
    (hI : ∀ k : ℕ, 0 < k →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ k}))))
    (hTor : ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
    ∀ (y : Fin e → Section2.StageAlgebra A D t p n),
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
        let _ := Module.compHom (koszulHomologySelf (φ ∘ y) i) ψ
        I ≤ Module.annihilator S (koszulHomologySelf (φ ∘ y) i) := by
  let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  dsimp only
  intro y hy i hi
  exact finiteParameterKoszul_positive_annihilator
    (Section2.stageAlgebra_algebraMap_injective A D t p n) φ hφ t hsop hres
    ψ I a j₀ ha hI hTor y hy i hi

end SerrePositivity.CLMST

end FiniteStageKoszulAnnihilatorPart

section ConditionalCohomologyVanishingPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.Section2

/-- The two conclusions of Corollary 4.0.4 follow from the explicit common inputs,
without using the literature statement or any perfectoid existence input in the proof. -/
lemma conditional_corollary_4_0_4
    {A D C S : Type u} [CommRing A] [IsNoetherianRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [CommRing C] [CommRing S]
    [Algebra A D] [Module.Finite A D] [Algebra A C] [Algebra D C] [IsScalarTower A D C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (hres : ∀ k : ℕ, IsKoszulResolution (fun j => t j ^ k))
    (φ : ∀ n : ℕ, Section2.StageAlgebra A D t p n →+* C)
    (hφ : ∀ (n : ℕ) (x : A), φ n (algebraMap D (Section2.StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (ψ : S →+* C) (I : Ideal S) (a : S) (j₀ : Fin e)
    (ha : ψ a = algebraMap A C (t j₀))
    (hI : ∀ k : ℕ, 0 < k →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ k}))))
    (hTor : ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    (∀ i : ℕ, i < e → ∀ s ∈ I,
      HomologicalAlgebra.localCohomologyScalarEndomorphism
        (IsLocalRing.maximalIdeal D) i C (ψ s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin e → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom (koszulHomologySelf (φ n ∘ y) i) ψ
          I ≤ Module.annihilator S (koszulHomologySelf (φ n ∘ y) i)) := by
  constructor
  · intro i hi s hs
    exact parameterLocalCohomologyScalarEndomorphism_eq_zero_of_baseIdeal_tor
      ψ I t hsop hres hTor i hi s hs
  · intro n
    exact finiteStageKoszul_positive_annihilator t p hsop hres n (φ n) (hφ n)
      ψ I a j₀ ha hI hTor

end SerrePositivity.CLMST

end ConditionalCohomologyVanishingPart

section RPerfdCohomologyInputsPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.Section2 _root_.IsLocalRing
attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {h : ℕ} (t : Fin h → A)

/-- Every power of the actual regular parameter system resolves its quotient,
including power zero. No regularity of RPerfd is used. -/
lemma parameter_power_isKoszulResolution
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdim : ringKrullDim A = h) (k : ℕ) :
    IsKoszulResolution (fun j => t j ^ k) :=
  isKoszulResolution_all_powers t ht
    (isWeaklyRegular_of_span_eq_maximalIdeal A t ht hdim) k

variable (D : Type u) [CommRing D] [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

/-- The selected RPerfd is derived p-complete for its original A-action. This
uses its existing perfectoidization property, without a torsion-free assumption. -/
lemma rPerfd_isModuleComplete :
    DerivedCompletion.IsModuleComplete A (p : A)
      (ModuleCat.of A (RPerfd A D t p hperf)) :=
  IsIntegralPerfectoid.isModuleComplete_algebra A (RPerfd A D t p hperf) p
    (isPerfectoidization_toMixedPerfectoid A D t p hperf).1

/-- The actual RPerfd derived tensor with every finite A-module is complete.
No completeness, p-regularity, or flatness is imposed on the test module. -/
lemma rPerfd_derivedTensor_isComplete (N : ModuleCat.{u} A) [Module.Finite A N] :
    DerivedCompletion.IsComplete A (p : A)
      ((boundedAboveDerivedTensorModuleFunctor
        (ModuleCat.of A (RPerfd A D t p hperf))).obj N) :=
  DerivedCompletion.boundedAboveDerivedTensor_isComplete_of_finite_regular A (p : A)
    (ModuleCat.of A (RPerfd A D t p hperf)) N (rPerfd_isModuleComplete A t D p hperf)

/-- The original Koszul-completion-to-power-cokernel comparison is a
quasi-isomorphism in the actual RPerfd tensor model for every finite test module. -/
lemma rPerfd_finiteCoefficientPowerComparison_quasiIso
    (N : ModuleCat.{u} A) [Module.Finite A N] :
    QuasiIso (DerivedCompletion.koszulPowerCokernelComparison (p : A)
      (DerivedCompletion.finiteCoefficientTensorModel A
        (ModuleCat.of A (RPerfd A D t p hperf)) N)) :=
  DerivedCompletion.finiteCoefficientPowerComparison_quasiIso A (p : A)
    (ModuleCat.of A (RPerfd A D t p hperf)) N (rPerfd_isModuleComplete A t D p hperf)

/-- Each original power cokernel is the actual derived tensor of the selected
RPerfd with N/pⁿN. N need not be finite, flat, regular, or complete. -/
def rPerfd_modulePowerDerivedTensorIso (N : ModuleCat.{u} A) (n : ℕ) :
    DerivedCategory.Q.obj (DerivedCompletion.powerCokernelComplex (p : A)
      ((moduleTensorCochainFunctor (extRes (projectiveResolution
        (ModuleCat.of A (RPerfd A D t p hperf))))).obj N) n) ≅
      (boundedAboveDerivedTensorModuleFunctor (ModuleCat.of A (RPerfd A D t p hperf))).obj
        (DerivedCompletion.modulePowerReduction (p : A) N n) :=
  DerivedCompletion.modulePowerDerivedTensorIso (p : A)
    (ModuleCat.of A (RPerfd A D t p hperf)) N n

/-- The original finite-test tensor is the holim of the ordinary quotient tower.
The selected perfectoidization and original A-action are unchanged. -/
def rPerfd_finiteCoefficientPowerHolimIso (N : ModuleCat.{u} A) [Module.Finite A N] :
    (boundedAboveDerivedTensorModuleFunctor (ModuleCat.of A (RPerfd A D t p hperf))).obj N ≅
      DerivedCategory.Q.obj (DerivedCompletion.modulePowerDerivedTensorHolimComplex A (p : A)
        (ModuleCat.of A (RPerfd A D t p hperf)) N) :=
  DerivedCompletion.finiteCoefficientPowerHolimIso A (p : A)
    (ModuleCat.of A (RPerfd A D t p hperf)) N (rPerfd_isModuleComplete A t D p hperf)

/-- Finite-test algebra-valued Tor is derived p-complete over the original
completed tower, using its existing action on the same RPerfd. -/
lemma rPerfd_torAlgebra_isModuleComplete (N : ModuleCat.{u} A) [Module.Finite A N] (i : ℕ) :
    DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p)
      ((ModuleCat.restrictScalars
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
          (((ModuleCat.extendScalars (algebraMap A (RPerfd A D t p hperf))).leftDerived i).obj N)) :=
  DerivedCompletion.torAlgebra_isModuleComplete_restrict_of_finite
    (RPerfd A D t p hperf) N (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf)) p
    (rPerfd_isModuleComplete A t D p hperf) i

/-- The original almost-Tor input is the actual completed-tower annihilator
condition on algebra-valued Tor, for arbitrary test modules. -/
lemma rPerfd_torAlgebra_annihilator_iff (N : ModuleCat.{u} A) (i : ℕ) (g : A) :
    (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g),
      torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) ↔
      (letI := Module.compHom
        (((ModuleCat.extendScalars (algebraMap A (RPerfd A D t p hperf))).leftDerived i).obj N)
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
       _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
         (algebraMap A (CompletedTower A t p) g) ≤ Module.annihilator (CompletedTower A t p)
           (((ModuleCat.extendScalars (algebraMap A (RPerfd A D t p hperf))).leftDerived i).obj N)) :=
  torAlgebraComparison_restricted_annihilator_iff (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g)) N i

/-- Both actual Tor-tower Milnor endpoints are complete over the original tower.
The test module need not be finite or complete, and lim¹ is retained. -/
lemma rPerfd_torMilnor_endpoints_isModuleComplete (N : ModuleCat.{u} A) (i : ℕ) :
    DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p)
      ((ModuleCat.restrictScalars
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
          (DerivedCompletion.modulePowerTorAlgebraLimit (p : A) (RPerfd A D t p hperf) N i)) ∧
    DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p)
      ((ModuleCat.restrictScalars
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
          (DerivedCompletion.modulePowerTorAlgebraLimOne (p : A) (RPerfd A D t p hperf) N i)) :=
  ⟨DerivedCompletion.modulePowerTorAlgebraLimit_isModuleComplete_restrict
    (RPerfd A D t p hperf) N i (CompletedTower A t p)
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf)) p,
   DerivedCompletion.modulePowerTorAlgebraLimOne_isModuleComplete_restrict
    (RPerfd A D t p hperf) N i (CompletedTower A t p)
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf)) p⟩

/-- The original positive-power torsion tests annihilate both actual Tor-tower endpoints. -/
lemma rPerfd_torMilnor_endpoints_annihilated (N : ModuleCat.{u} A) (i : ℕ) (g : A)
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L i
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g) ≤
      Module.annihilator (CompletedTower A t p)
        ((ModuleCat.restrictScalars
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
            (DerivedCompletion.modulePowerTorAlgebraLimit (p : A) (RPerfd A D t p hperf) N i)) ∧
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g) ≤
      Module.annihilator (CompletedTower A t p)
        ((ModuleCat.restrictScalars
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
            (DerivedCompletion.modulePowerTorAlgebraLimOne (p : A) (RPerfd A D t p hperf) N i)) :=
  ⟨DerivedCompletion.modulePowerTorAlgebraLimit_annihilated (p : A)
    (RPerfd A D t p hperf) N i (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf)) _ hTor,
   DerivedCompletion.modulePowerTorAlgebraLimOne_annihilated (p : A)
    (RPerfd A D t p hperf) N i (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf)) _ hTor⟩

/-- The actual coefficient-linear Milnor sequence over the original completed tower. -/
def rPerfd_torMilnorShortComplex (N : ModuleCat.{u} A) [Module.Finite A N] (i : ℕ) :
    ShortComplex (ModuleCat.{u} (CompletedTower A t p)) :=
  DerivedCompletion.torAlgebraMilnorShortComplexOver (p : A) (RPerfd A D t p hperf) N
    (rPerfd_isModuleComplete A t D p hperf) i (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))

lemma rPerfd_torMilnorShortComplex_shortExact
    (N : ModuleCat.{u} A) [Module.Finite A N] (i : ℕ) :
    (rPerfd_torMilnorShortComplex A t D p hperf N i).ShortExact :=
  DerivedCompletion.torAlgebraMilnorShortComplexOver_shortExact (p : A) (RPerfd A D t p hperf) N
    (rPerfd_isModuleComplete A t D p hperf) i (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))

/-- The full actual almost-Tor input follows from the two still-explicit inputs:
power-torsion tests and complete almost extension closure over the original tower. -/
lemma rPerfd_tor_eq_zero_of_power_torsion_and_extensions (g : A)
    (hExt : DerivedCompletion.CompleteIdealExtensionClosed (CompletedTower A t p)
      (p : CompletedTower A t p) (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)))
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0)
    (N : ModuleCat.{u} A) (i : ℕ) (hi : 0 < i) (s : CompletedTower A t p)
    (hs : s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) :
    torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0 :=
  DerivedCompletion.tor_eq_zero_of_power_torsion_and_complete_extensions p
    (RPerfd A D t p hperf) (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))
    (rPerfd_isModuleComplete A t D p hperf) hExt hTor N i hi s hs

/-- The original completed quotient multiplication supplies the extension input
for full Tor annihilation; torsion tests remain explicit. -/
lemma rPerfd_tor_eq_zero_of_power_torsion_and_completed_quotient_mul (g : A)
    (hμ : IsIso ((DerivedCompletion.derivedComplexCompletionFunctor
      (CompletedTower A t p) (p : CompletedTower A t p)).map
        (boundedAboveDerivedAlgebraMul (R := CompletedTower A t p)
          ((CompletedTower A t p) ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g))).hom))
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0)
    (N : ModuleCat.{u} A) (i : ℕ) (hi : 0 < i) (s : CompletedTower A t p)
    (hs : s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) :
    torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0 :=
  DerivedCompletion.tor_eq_zero_of_power_torsion_and_complete_extensions p
    (RPerfd A D t p hperf) (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))
    (rPerfd_isModuleComplete A t D p hperf)
    (DerivedCompletion.completeIdealExtensionClosed_of_completed_quotient_mul_isIso
      (p : CompletedTower A t p) _ hμ) hTor N i hi s hs

/-- Full Tor annihilation from explicit torsion tests and scalar surjectivity on
the actual first self-Tor of the original almost quotient. -/
lemma rPerfd_tor_eq_zero_of_power_torsion_and_quotientTorOne (g : A)
    (hQ : Function.Surjective (fun x : TorModule (CompletedTower A t p) 1
      ((CompletedTower A t p) ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g))
      ((CompletedTower A t p) ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) => (p : CompletedTower A t p) • x))
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0)
    (N : ModuleCat.{u} A) (i : ℕ) (hi : 0 < i) (s : CompletedTower A t p)
    (hs : s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) :
    torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0 :=
  DerivedCompletion.tor_eq_zero_of_power_torsion_and_quotientTorOne p
    (RPerfd A D t p hperf) (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))
    (rPerfd_isModuleComplete A t D p hperf) hTor hQ N i hi s hs

/-- The actual finite-stage map has the base compatibility required by the
Koszul/local-cohomology theorem. -/
lemma toRPerfd_algebraMap_A (n : ℕ) (x : A) :
    toRPerfd A D t p hperf n
      (algebraMap D (Section2.StageAlgebra A D t p n) (algebraMap A D x)) =
        algebraMap A (RPerfd A D t p hperf) x := by
  rw [toRPerfd_algebraMap_D]
  exact (IsScalarTower.algebraMap_apply A D (RPerfd A D t p hperf) x).symm

/-- The distinguished p-coordinate agrees under the original completed-tower
action on RPerfd. -/
lemma rPerfd_p_coordinate (j₀ : Fin h) (htp : t j₀ = (p : A)) :
    algebraMap (CompletedTower A t p) (RPerfd A D t p hperf)
      (p : CompletedTower A t p) = algebraMap A (RPerfd A D t p hperf) (t j₀) := by
  simp only [htp, map_natCast]

/-- Supply the full Tor input from finitely generated tests on the same selected
RPerfd. No completeness assumption is imposed on the arbitrary test module. -/
lemma rPerfd_tor_eq_zero_of_finite (g : A)
    (hTor : ∀ (N : ModuleCat.{u} A), Module.Finite A N → ∀ (i : ℕ), 0 < i →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0)
    (N : ModuleCat.{u} A) (i : ℕ) (hi : 0 < i)
    (s : CompletedTower A t p)
    (hs : s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) :
    torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0 :=
  torCoefficientScalarEndomorphism_eq_zero_of_finite (RPerfd A D t p hperf) i
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s)
    (fun M hM => hTor M hM i hi s hs) N

/-- Apply the common comparison to the selected RPerfd and the actual almost
ideal. The two remaining inputs are kept at their full original quantifiers. -/
lemma rPerfd_cohomology_vanishing_of_tor_idempotent
    [IsLocalRing D] [IsNoetherianRing D]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hI : ∀ k : ℕ, 0 < k → IsIdempotentElem
      ((_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)).map
          (Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p) ^ k}))))
    (hTor : ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N j
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
    (∀ i : ℕ, i < h →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i
          (RPerfd A D t p hperf)
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin h → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom
            (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p)
                (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)) := by
  exact conditional_corollary_4_0_4 t p hsop
    (parameter_power_isKoszulResolution A t ht hdim)
    (fun n => (toRPerfd A D t p hperf n).toRingHom)
    (toRPerfd_algebraMap_A A t D p hperf)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g))
    (p : CompletedTower A t p) j₀ (rPerfd_p_coordinate A t D p hperf j₀ htp) hI hTor

/-- Both original Cor 4.0.4 conclusions from the completed standard quotient
multiplication and power-torsion Tor tests; image idempotence is derived. -/
lemma rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_power_torsion
    [IsLocalRing D] [IsNoetherianRing D]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hμ : IsIso ((DerivedCompletion.derivedComplexCompletionFunctor
      (CompletedTower A t p) (p : CompletedTower A t p)).map
        (boundedAboveDerivedAlgebraMul (R := CompletedTower A t p)
          ((CompletedTower A t p) ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g))).hom))
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
    (∀ i : ℕ, i < h →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i
          (RPerfd A D t p hperf)
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin h → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom
            (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p)
                (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)) :=
  rPerfd_cohomology_vanishing_of_tor_idempotent A t D p hperf ht hdim hsop j₀ htp g
    (fun k _ => DerivedCompletion.ideal_mod_power_idempotent_of_completed_quotient_mul_isIso
      (p : CompletedTower A t p) _ hμ k)
    (rPerfd_tor_eq_zero_of_power_torsion_and_completed_quotient_mul A t D p hperf g hμ hTor)

end SerrePositivity.CLMST

end RPerfdCohomologyInputsPart

section RPerfdTorBaseChangePart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.Section2 _root_.IsLocalRing
attribute [local instance] HasDerivedCategory.standard
variable (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {h : ℕ} (t : Fin h → A)
    (D : Type u) [CommRing D] [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

/-- The tower-side power-torsion Tor input gives the original A-side tests. -/
lemma rPerfd_power_torsion_tor_eq_zero_of_completedTower (g : A)
    (hTor : ∀ (L : ModuleCat.{u} (CompletedTower A t p)) (k : ℕ), 0 < k →
      (∀ x : L, (p : CompletedTower A t p) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0)
    (N : ModuleCat.{u} A) (k : ℕ) (hk : 0 < k)
    (hN : ∀ x : N, (p : A) ^ k • x = 0)
    (j : ℕ) (hj : 0 < j) (s : CompletedTower A t p)
    (hs : s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) :
    torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N j
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0 := by
  letI := flat_completedTower_over_base A t p
  exact powerTorsionTorInput_of_flat_baseChange (R := A) (B := CompletedTower A t p)
    (C := RPerfd A D t p hperf) p _ hTor N k hk hN j hj s hs

/-- Both Cor 4.0.4 conclusions from the original completed quotient product and
the original tower-side power-torsion tests. -/
lemma rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_tower_power_torsion
    [IsLocalRing D] [IsNoetherianRing D]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hμ : IsIso ((DerivedCompletion.derivedComplexCompletionFunctor
      (CompletedTower A t p) (p : CompletedTower A t p)).map
        (boundedAboveDerivedAlgebraMul (R := CompletedTower A t p)
          ((CompletedTower A t p) ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g))).hom))
    (hTor : ∀ (L : ModuleCat.{u} (CompletedTower A t p)) (k : ℕ), 0 < k →
      (∀ x : L, (p : CompletedTower A t p) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
    (∀ i : ℕ, i < h →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i
          (RPerfd A D t p hperf)
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin h → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom
            (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p)
                (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)) :=
  rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_power_torsion
    A t D p hperf ht hdim hsop j₀ htp g hμ
    (rPerfd_power_torsion_tor_eq_zero_of_completedTower A t D p hperf g hTor)

/-- The actual quotient product is proved; only the original tower-side Tor tests remain explicit. -/
lemma rPerfd_cohomology_vanishing_of_tower_power_torsion
    [IsLocalRing D] [IsNoetherianRing D]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hTor : ∀ (L : ModuleCat.{u} (CompletedTower A t p)) (k : ℕ), 0 < k →
      (∀ x : L, (p : CompletedTower A t p) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
    (∀ i : ℕ, i < h →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i
          (RPerfd A D t p hperf)
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin h → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom
            (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p)
                (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)) :=
  rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_tower_power_torsion
    A t D p hperf ht hdim hsop j₀ htp g
    (BhattScholze.perfectoidIdeal_completedQuotientMul_map_isIso (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) hTor

end SerrePositivity.CLMST

end RPerfdTorBaseChangePart

section KLCohomologyFromExcisionPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.Section2 _root_.IsLocalRing
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard

/-- The full original low local-cohomology and all finite-stage Koszul
conclusions follow from excision on AIC perfectoid extensions of the completed
tower. No Tor-zero hypothesis is supplied by the caller. -/
theorem rPerfd_cohomology_vanishing_of_finiteComparison_excision
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {h : ℕ} (t : Fin h → A)
    (D : Type u) [CommRing D] [Algebra A D] [Module.Finite A D]
    [IsLocalRing D] [IsNoetherianRing D]
    (p : ℕ) [Fact p.Prime] (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hetale : letI := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (hExcision : ∀ (E : Type u) [CommRing E] [Algebra (CompletedTower A t p) E],
      IsIntegralPerfectoid E p → IsAbsolutelyIntegrallyClosed E → BhattScholze.KLFiniteComparisonExcision E p) :
    (∀ i : ℕ, i < h →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i
          (RPerfd A D t p hperf)
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin h → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom
            (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p)
                (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)) := by
  let : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D
  let : Algebra.FinitePresentation A D := inferInstance
  let f : ((CompletedTower A t p) ⊗[A] D) →ₐ[CompletedTower A t p]
      (RPerfd A D t p hperf) :=
    { toMixedPerfectoid A D t p hperf with commutes' := fun _ => rfl }
  have hf : IsPerfectoidization p f.toRingHom := isPerfectoidization_toMixedPerfectoid A D t p hperf
  let := GenericEtale.awayAlgebra A D g
  have he := etaleAway_tensor_baseChange (B := CompletedTower A t p) g hetale
  let := GenericEtale.awayAlgebra (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D)
    (algebraMap A (CompletedTower A t p) g)
  have hTor := BhattScholze.perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision
    p hperf hExcision (algebraMap A (CompletedTower A t p) g) f hf he
  exact rPerfd_cohomology_vanishing_of_tower_power_torsion A t D p hperf
    ht hdim hsop j₀ htp g (fun N k _hk hN i hi s hs => hTor N k hN i hi s hs)

end SerrePositivity.CLMST

end KLCohomologyFromExcisionPart

section Corollary404Part

set_option linter.unusedVariables false

namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2

/--
## 概要
Cor 4.0.4 の原典署名の両消滅を、BS の二つの入力から証明する。

## 方針
perfectoid な絶対整閉拡大上の有限比較 excision を供給して、全冪ねじれ試験を得る。
全加群版と KL-Q の既存の合流で、元の ideal の全元による両消滅へ戻す。

## 規約
原典署名の全仮定を保持し、g の選択とパラメータ系の量化を変更しない。

## 使われ方
corollary_4_0_4 の同じ署名の証明として用いる。
-/
theorem corollary_4_0_4
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) :
    (∀ i : ℕ, i < h → ∀ a ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g),
      HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i
        (RPerfd A D t p hperf) (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) a) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin h → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom
            (koszulHomologySelf (fun j ↦ toRPerfd A D t p hperf n (y j)) i)
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p)
                (koszulHomologySelf (fun j ↦ toRPerfd A D t p hperf n (y j)) i)) := by
  exact rPerfd_cohomology_vanishing_of_finiteComparison_excision A t D p hperf
    ht hdimA hsop ⟨0, hpos⟩ htp g hEtale
    (fun E _ _ hE _ => BhattScholze.klFiniteComparisonExcision_of_perfectoid E p hE)

end SerrePositivity.CLMST

end Corollary404Part

section CohomologyVanishingPart

namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2

variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 一つの固定したエタール開集合の元から、D の全パラメータ系に対する Koszul 消滅を導く。 -/
theorem parameter_koszul_annihilates_of_etale (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℕ) (hi : 0 < i) :
    let _ := Module.compHom
      (koszulHomologySelf (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) i)
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) ≤
        Module.annihilator (CompletedTower A t p)
          (koszulHomologySelf (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) i) := by
  let : IsLocalRing (Section2.StageAlgebra A D t p 0) := Section2.stage0IsLocalRing A D t p
  let : Module.Finite D (Section2.StageAlgebra A D t p 0) := Section2.stage0ModuleFinite A D t p
  have hz0 := hz.map_finite (Section2.StageAlgebra A D t p 0)
    (Section2.stage0_algebraMap_injective A D t p)
  have hvan := (corollary_4_0_4 A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf g hg hEtale).2 0 (algebraMap D _ ∘ z) hz0 i hi
  have hseq : (fun j ↦ toRPerfd A D t p hperf 0
      ((algebraMap D (Section2.StageAlgebra A D t p 0) ∘ z) j)) =
      (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) := by
    funext j
    exact toRPerfd_algebraMap_D A D t p hperf 0 (z j)
  rw [hseq] at hvan
  exact hvan

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 有限エタール化で g を選び、Corollary 4.0.4 を全パラメータ系へ同時に適用する。
非零元の存在そのものは、文献の消滅引用の結論に含めない。 -/
theorem exists_perfectoidIdeal_annihilates_koszul :
    ∃ g : A, g ≠ 0 ∧ ∀ (z : Fin h → D), IsSystemOfParameters D z →
      ∀ i : ℕ, 0 < i →
        let _ := Module.compHom
          (koszulHomologySelf (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) i)
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g) ≤
            Module.annihilator (CompletedTower A t p)
              (koszulHomologySelf (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) i) := by
  obtain ⟨g, hg, _, hEtale⟩ := exists_finite_etale_away A D hinj
  refine ⟨g, hg, fun z hz i hi ↦ ?_⟩
  exact parameter_koszul_annihilates_of_etale A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf g hg hEtale z hz i hi

end SerrePositivity.CLMST

end CohomologyVanishingPart

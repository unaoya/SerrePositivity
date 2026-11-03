module

public import SerrePositivity.BhattScholze.Perfectoidization.Cone
public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Proof
public import SerrePositivity.CommutativeAlgebra.Localization.EtaleAway
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.TensorProduct.Finite
public import SerrePositivity.CLMST.Algebra
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion

/-! # Prop 2.4.7 の帰結：標準写像の核・余核の制御

## 概要

錐の零射から、標準写像の核・余核が同じ冪で零化されることを示し、始域で `g` の作用が単射なら標準写像の単射性も導く（`injective_and_exists_pow_annihilates_coker`）。平坦な基底変更、完備化した根の塔の上（`completedTensor_injective_and_exists_pow_annihilates_coker`）、非単元のエタール開集合と正の零化指数（`exists_nonunit_completedTensor_positive_isogeny`）に適用する。

## 方針

`g` の正則性は原典の引用に混ぜず、具体的な適用で確かめる条件として保つ。

## 規約

CLMST Prop 2.4.7 の適用。旧 `CLMST/PerfectoidIsogeny`・`Inputs/PerfectoidIsogeny`・`TensorIsogeny`・`CompletedTensorIsogeny`・`NonunitIsogeny`。

## 使われ方

`CLMST/ParameterQuotientLength`（Prop 4.0.14）。
-/

@[expose] public noncomputable section

universe u

section PerfectoidIsogenyPart

namespace SerrePositivity.CLMST
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

end SerrePositivity.CLMST

end PerfectoidIsogenyPart

section PerfectoidIsogenyPart

namespace SerrePositivity.CLMST
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (J : Ideal R) (hJ : J.FG)
    (hEtale : ∀ g ∈ J, let _ := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (hbounded : ∃ N : ℕ, ∀ (n : ℕ) (s : S),
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)

include hJ hEtale hbounded in
/-- 原典の錐の零射から、各 g∈J に対して核・余核を同じ冪で零化できる。 -/
theorem exists_pow_annihilates_ker_coker (g : R) (hg : g ∈ J) :
    ∃ N : ℕ,
      (∀ x : (BhattScholze.perfectoidizationModuleMap R S p hR).ker, (g ^ N) • x = 0) ∧
      (∀ x : (Perfectoidization R S p hR) ⧸
        (BhattScholze.perfectoidizationModuleMap R S p hR).range, (g ^ N) • x = 0) := by
  obtain ⟨N, hN⟩ := proposition_2_4_7 R S p hR J hJ hEtale hbounded g hg
  exact ⟨N, moduleMapCone_pow_scalar_eq_zero_annihilates R
    (BhattScholze.perfectoidizationModuleMap R S p hR) g N hN⟩

include hJ hEtale hbounded in
/-- 始域で g が正則なら標準写像は単射で、余核を g の同じ冪で消せる。
単射性そのものは外部引用の結論に追加せず、錐と正則性から証明する。 -/
theorem injective_and_exists_pow_annihilates_coker (g : R) (hg : g ∈ J)
    (hregular : IsSMulRegular S g) :
    Function.Injective (BhattScholze.perfectoidizationModuleMap R S p hR) ∧
      ∃ N : ℕ, ∀ x : (Perfectoidization R S p hR) ⧸
        (BhattScholze.perfectoidizationModuleMap R S p hR).range, (g ^ N) • x = 0 := by
  obtain ⟨N, hN⟩ := proposition_2_4_7 R S p hR J hJ hEtale hbounded g hg
  obtain ⟨hinj, hcoker⟩ := moduleMapCone_pow_scalar_eq_zero_injective_of_regular R
    (BhattScholze.perfectoidizationModuleMap R S p hR) g N hregular hN
  exact ⟨hinj, N, hcoker⟩

end SerrePositivity.CLMST

end PerfectoidIsogenyPart

section TensorIsogenyPart

open scoped TensorProduct
namespace SerrePositivity.CLMST
attribute [local instance] HasDerivedCategory.standard

variable (A R D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing R] [CommRing D] [Algebra A R] [Algebra A D]
    [Module.Finite A D] [Module.Flat A R]

local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

/-- 平坦な perfectoid 基底への有限代数の基底変更に、命題2.4.7を適用する。
主イデアル全体のエタール条件、p 冪ねじれの有界性、g の正則性を個別に供給する。 -/
theorem tensor_injective_and_exists_pow_annihilates_coker
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : A)
    (hg : IsSMulRegular D (algebraMap A D g)) (hp : IsSMulRegular D (p : D))
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) :
    Function.Injective (BhattScholze.perfectoidizationModuleMap R (R ⊗[A] D) p hR) ∧
      ∃ N : ℕ, ∀ x : (Perfectoidization R (R ⊗[A] D) p hR) ⧸
        (BhattScholze.perfectoidizationModuleMap R (R ⊗[A] D) p hR).range,
        (algebraMap A R g ^ N) • x = 0 := by
  have hregular := isSMulRegular_tensorProduct_of_flat A R D g hg
  have hp' : IsSMulRegular (R ⊗[A] D) (p : R ⊗[A] D) := by
    have hbase := isSMulRegular_tensorProduct_of_flat A R D (p : A) (by simpa using hp)
    change Function.Injective (fun x : R ⊗[A] D ↦ algebraMap A R (p : A) • x) at hbase
    change Function.Injective (fun x : R ⊗[A] D ↦ (p : R ⊗[A] D) * x)
    simpa [Algebra.smul_def] using hbase
  have hbounded := exists_pow_torsion_bound_of_isSMulRegular (R ⊗[A] D) p hp'
  have het : ∀ x ∈ Ideal.span {algebraMap A R g},
      let _ := GenericEtale.awayAlgebra R (R ⊗[A] D) x
      Algebra.Etale (Localization.Away x)
        (Localization.Away (algebraMap R (R ⊗[A] D) x)) := by
    intro x hx
    exact GenericEtale.etale_away_baseChange_of_mem_span_singleton A R D g x hx hEtale
  exact injective_and_exists_pow_annihilates_coker R (R ⊗[A] D) p hR
    (Ideal.span {algebraMap A R g}) (Submodule.fg_span_singleton _) het hbounded
    (algebraMap A R g) (Ideal.subset_span (Set.mem_singleton _)) hregular

end SerrePositivity.CLMST

end TensorIsogenyPart

section CompletedTensorIsogenyPart

open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2
attribute [local instance] HasDerivedCategory.standard

variable (A D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

/-- 具体的な完備塔の平坦性を供給して、テンソル代数の isogeny を導く。 -/
theorem completedTensor_injective_and_exists_pow_annihilates_coker
    (g : A) (hg : IsSMulRegular D (algebraMap A D g)) (hp : IsSMulRegular D (p : D))
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) :
    Function.Injective (BhattScholze.perfectoidizationModuleMap (CompletedTower A t p)
      ((CompletedTower A t p) ⊗[A] D) p hperf) ∧
      ∃ N : ℕ, ∀ x : (RPerfd A D t p hperf) ⧸
        (BhattScholze.perfectoidizationModuleMap (CompletedTower A t p)
          ((CompletedTower A t p) ⊗[A] D) p hperf).range,
        (algebraMap A (CompletedTower A t p) g ^ N) • x = 0 := by
  let := flat_completedTower_over_base A t p
  exact tensor_injective_and_exists_pow_annihilates_coker A (CompletedTower A t p) D
    p hperf g hg hp hEtale

/-- 標数零の有限整域拡大では、g≠0と係数写像の単射性から必要な正則性を供給できる。 -/
theorem completedTensor_injective_and_exists_pow_annihilates_coker_of_domain
    [IsDomain D] [CharZero D] (hinj : Function.Injective (algebraMap A D))
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) :
    Function.Injective (BhattScholze.perfectoidizationModuleMap (CompletedTower A t p)
      ((CompletedTower A t p) ⊗[A] D) p hperf) ∧
      ∃ N : ℕ, ∀ x : (RPerfd A D t p hperf) ⧸
        (BhattScholze.perfectoidizationModuleMap (CompletedTower A t p)
          ((CompletedTower A t p) ⊗[A] D) p hperf).range,
        (algebraMap A (CompletedTower A t p) g ^ N) • x = 0 := by
  have hgD : algebraMap A D g ≠ 0 := fun hzero ↦ hg (hinj (hzero.trans (map_zero _).symm))
  have hpD : (p : D) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply completedTensor_injective_and_exists_pow_annihilates_coker A D t p hperf g
    (fun x y hxy ↦ mul_left_cancel₀ hgD hxy)
    (fun x y hxy ↦ mul_left_cancel₀ hpD hxy) hEtale

/-- 同じ具体的 isogeny により、既存の選択された普遍環への標準環準同型も単射。 -/
theorem toMixedPerfectoid_injective_of_domain
    [IsDomain D] [CharZero D] (hinj : Function.Injective (algebraMap A D))
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) :
    Function.Injective (toMixedPerfectoid A D t p hperf) :=
  (completedTensor_injective_and_exists_pow_annihilates_coker_of_domain A D t p hperf
    hinj g hg hEtale).1

/-- 有限な標数零の整域拡大では、適切な非零 g の選択も一般エタール性から供給する。 -/
theorem exists_completedTensor_isogeny [IsDomain A] [IsDomain D] [CharZero D]
    (hinj : Function.Injective (algebraMap A D)) :
    ∃ g : A, g ≠ 0 ∧
      Function.Injective (toMixedPerfectoid A D t p hperf) ∧
      ∃ N : ℕ, ∀ x : (RPerfd A D t p hperf) ⧸
        (BhattScholze.perfectoidizationModuleMap (CompletedTower A t p)
          ((CompletedTower A t p) ⊗[A] D) p hperf).range,
        (algebraMap A (CompletedTower A t p) g ^ N) • x = 0 := by
  obtain ⟨g, hg, he⟩ := GenericEtale.exists_finite_etale_away_of_charZero A D hinj
  obtain ⟨hinjC, hbound⟩ :=
    completedTensor_injective_and_exists_pow_annihilates_coker_of_domain A D t p hperf
      hinj g hg he.2
  exact ⟨g, hg, hinjC, hbound⟩

end SerrePositivity.CLMST

end CompletedTensorIsogenyPart

section NonunitIsogenyPart

open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2 IsLocalRing
attribute [local instance] HasDerivedCategory.standard

variable (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [CommRing D] [IsLocalRing D] [IsDomain D] [CharZero D]
    [Algebra A D] [Module.Finite A D] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- エタールな開集合を p 倍で縮め、非零かつ非単元の元を選ぶ。 -/
theorem exists_nonzero_nonunit_etale_away
    (hinj : Function.Injective (algebraMap A D)) (hp : (p : A) ∈ maximalIdeal A) :
    ∃ g : A, g ≠ 0 ∧ g ∈ maximalIdeal A ∧ algebraMap A D g ∈ maximalIdeal D ∧
      (let _ := GenericEtale.awayAlgebra A D g
       Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) := by
  obtain ⟨g₀, hg₀, hEtale⟩ := GenericEtale.exists_finite_etale_away_of_charZero A D hinj
  let g := (p : A) * g₀
  have hpA : (p : A) ≠ 0 := by
    intro hzero
    have hpD : (p : D) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (algebraMap A D) hzero
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hpD
  have hg : g ≠ 0 := mul_ne_zero hpA hg₀
  have hgm : g ∈ maximalIdeal A := (maximalIdeal A).mul_mem_right g₀ hp
  have hgmD : algebraMap A D g ∈ maximalIdeal D :=
    (maximalIdeal_map_le_of_finite_of_injective A D hinj)
      (Ideal.mem_map_of_mem (algebraMap A D) hgm)
  let : Algebra.FinitePresentation A D := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hmem : g ∈ Ideal.span {g₀} := (Ideal.span {g₀}).mul_mem_left (p : A)
    (Ideal.subset_span (Set.mem_singleton g₀))
  exact ⟨g, hg, hgm, hgmD,
    GenericEtale.etale_away_of_mem_span_singleton A D g₀ g hmem hEtale.2⟩

local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

/-- 同じ非単元で、isogeny の零化指数を正に選べる。 -/
theorem exists_nonunit_completedTensor_positive_isogeny
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (hinj : Function.Injective (algebraMap A D)) (hp : (p : A) ∈ maximalIdeal A) :
    ∃ (g : A) (N : ℕ), g ≠ 0 ∧ g ∈ maximalIdeal A ∧
      algebraMap A D g ∈ maximalIdeal D ∧ 0 < N ∧
      (let _ := GenericEtale.awayAlgebra A D g
       Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) ∧
      Function.Injective (toMixedPerfectoid A D t p hperf) ∧
      (∀ x : (RPerfd A D t p hperf) ⧸
        (BhattScholze.perfectoidizationModuleMap (CompletedTower A t p)
          ((CompletedTower A t p) ⊗[A] D) p hperf).range,
        (algebraMap A (CompletedTower A t p) g) ^ N • x = 0) := by
  obtain ⟨g, hg, hgm, hgmD, hEtale⟩ := exists_nonzero_nonunit_etale_away A D p hinj hp
  obtain ⟨hinjC, N, hN⟩ := completedTensor_injective_and_exists_pow_annihilates_coker_of_domain
    A D t p hperf hinj g hg hEtale
  refine ⟨g, N + 1, hg, hgm, hgmD, by omega, hEtale, hinjC, ?_⟩
  intro x
  rw [pow_succ', mul_smul, hN x, smul_zero]

end SerrePositivity.CLMST

end NonunitIsogenyPart

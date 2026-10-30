module

public import SerrePositivity.CLMST.CompletedTensorIsogeny
public import SerrePositivity.CommutativeAlgebra.Localization.EtaleAway
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion

/-! # 非単元のエタール開集合と正の零化指数

エタール開集合の元を p 倍して極大イデアルに入れ、正の零化指数を選ぶ。
単元や零指数の場合分けを列変更へ持ち込まず、既存の isogeny と接続する。
-/

@[expose] public noncomputable section
universe u
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
        (perfectoidizationModuleMap (CompletedTower A t p)
          ((CompletedTower A t p) ⊗[A] D) p hperf).range,
        (algebraMap A (CompletedTower A t p) g) ^ N • x = 0) := by
  obtain ⟨g, hg, hgm, hgmD, hEtale⟩ := exists_nonzero_nonunit_etale_away A D p hinj hp
  obtain ⟨hinjC, N, hN⟩ := completedTensor_injective_and_exists_pow_annihilates_coker_of_domain
    A D t p hperf hinj g hg hEtale
  refine ⟨g, N + 1, hg, hgm, hgmD, by omega, hEtale, hinjC, ?_⟩
  intro x
  rw [pow_succ', mul_smul, hN x, smul_zero]

end SerrePositivity.CLMST

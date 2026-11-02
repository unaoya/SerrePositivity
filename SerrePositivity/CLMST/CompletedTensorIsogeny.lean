module

public import SerrePositivity.CLMST.TensorIsogeny
public import SerrePositivity.CLMST.Algebra
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion

/-! # 完備化した根の塔上の具体的な isogeny

共通の完備化の平坦性を根の塔へ適用し、A∞⊗_A D の標準 perfectoid 化写像の
単射性と余核の冪による零化を導く。完備塔の平坦性を利用側へ未知の仮定として渡さない。
perfectoid 性と命題2.4.7の文献入力は、一般可換環論の確認とは区別する。
-/

@[expose] public noncomputable section
universe u
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

import SerrePositivity.BhattScholze.Results.PerfectoidAlmost
import SerrePositivity.BhattScholze.Perfectoidization.Lemma103PerfectoidTensor
import SerrePositivity.BhattScholze.Results.PerfectoidIdealLemma103
import SerrePositivity.BhattScholze.Results.PerfectoidIdealIdempotent
import SerrePositivity.BhattScholze.Results.PerfectoidAlmostExtension
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorShortExact
import SerrePositivity.CommutativeAlgebra.PerfectTorIndependence.Basic
import Mathlib.Util.AssertNoSorry

/-! B5 の公開宣言と、指定された Tor 入力の正確な型の監査。 -/
assert_no_sorry SerrePositivity.BhattScholze.lemma103_perfectoidTensor
#print axioms SerrePositivity.BhattScholze.lemma103_perfectoidTensor

open CategoryTheory CategoryTheory.Limits SerrePositivity
universe u

-- 目標ファイルの hTor の型をそのまま満たす。追加仮定ではない。
example (p : ℕ) [Fact p.Prime] :
    ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra A C]
      [CharP A p] [CharP B p] [CharP C p]
      [PerfectRing A p] [PerfectRing B p] [PerfectRing C p],
      ∀ i : ℕ, 0 < i →
        IsZero (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A B)).obj
          (ModuleCat.of A C)) := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _
  exact tor_vanishing_of_perfect p

assert_no_sorry SerrePositivity.tor_vanishing_of_perfect
#print axioms SerrePositivity.tor_vanishing_of_perfect

assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_isZero_of_shortExact_rightMap_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_shortExact_leftMap_isIso_of_isZero
#print axioms SerrePositivity.DerivedCompletion.completedTensor_isZero_of_shortExact_rightMap_isIso
#print axioms SerrePositivity.DerivedCompletion.completedTensor_shortExact_leftMap_isIso_of_isZero

assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedQuotientTensorIdeal_isZero
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedQuotientTensorIdeal_isZero

assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedIdealTensorQuotient_isZero
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedIdealTensorQuotient_isZero

assert_no_sorry SerrePositivity.BhattScholze.boundedAboveDerivedIdealMul
#print axioms SerrePositivity.BhattScholze.boundedAboveDerivedIdealMul

assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedIdealMul_isIso
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedIdealMul_isIso

assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_quotientIdeal_isModuleComplete
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_quotientIdeal_isModuleComplete

assert_no_sorry SerrePositivity.BhattScholze.completedDerivedIdealMul
#print axioms SerrePositivity.BhattScholze.completedDerivedIdealMul

assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedDerivedIdealMul_isIso
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedDerivedIdealMul_isIso

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_isModuleComplete
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_isModuleComplete

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_lemma103
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_lemma103

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_conormal_pow_smul_surjective
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_conormal_pow_smul_surjective

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_eq_square_sup_pow_mul
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_eq_square_sup_pow_mul

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdealMod_idempotent
#print axioms SerrePositivity.BhattScholze.perfectoidIdealMod_idempotent

assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_isZero_whiskerRight
#print axioms SerrePositivity.DerivedCompletion.completedTensor_isZero_whiskerRight

assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_isZero_of_action_retract
#print axioms SerrePositivity.DerivedCompletion.completedTensor_isZero_of_action_retract

assert_no_sorry SerrePositivity.DerivedCompletion.derivedTensor_module_action_retract
#print axioms SerrePositivity.DerivedCompletion.derivedTensor_module_action_retract

assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_isZero_of_algebraModule
#print axioms SerrePositivity.DerivedCompletion.completedTensor_isZero_of_algebraModule

assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_shortExact_rightMap_isIso_of_isZero
#print axioms SerrePositivity.DerivedCompletion.completedTensor_shortExact_rightMap_isIso_of_isZero

assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_isZero_of_shortExact
#print axioms SerrePositivity.DerivedCompletion.completedTensor_isZero_of_shortExact

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_completedQuotientMul
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_completedQuotientMul

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_completedQuotientMul_isIso
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_completedQuotientMul_isIso

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_completedTensor_isZero_of_isAlmostZero
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_completedTensor_isZero_of_isAlmostZero

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_isAlmostZero_of_completedTensor_isZero
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_isAlmostZero_of_completedTensor_isZero

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_isAlmostZero_extension
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_isAlmostZero_extension

-- レーン K が受け取る定理の型を、指定された引数順・仮定で検査する。
example
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ : DerivedCompletion.IsModuleComplete R (p : R) S.X₁)
    (h₂ : DerivedCompletion.IsModuleComplete R (p : R) S.X₂)
    (h₃ : DerivedCompletion.IsModuleComplete R (p : R) S.X₃)
    (hX₁ : Almost.IsAlmostZero (perfectoidIdeal R p hR g) S.X₁)
    (hX₃ : Almost.IsAlmostZero (perfectoidIdeal R p hR g) S.X₃) :
    Almost.IsAlmostZero (perfectoidIdeal R p hR g) S.X₂ :=
  BhattScholze.perfectoidIdeal_isAlmostZero_extension R p hR g S hS h₁ h₂ h₃ hX₁ hX₃

-- BasicSetup へ渡す mod p^N 冪等性も、同じ略記・等式の型で検査する。
example (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (N : ℕ) :
    CLMST.perfectoidIdealMod R p hR g N * CLMST.perfectoidIdealMod R p hR g N =
      CLMST.perfectoidIdealMod R p hR g N :=
  BhattScholze.perfectoidIdealMod_idempotent R p hR g N

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_quotient_isIntegralPerfectoid
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_quotient_isIntegralPerfectoid

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_conormal_smul_bijective
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_conormal_smul_bijective

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_conormal_completion_isZero
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_conormal_completion_isZero

assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdeal_conormal_mod_p_isZero
#print axioms SerrePositivity.BhattScholze.perfectoidIdeal_conormal_mod_p_isZero

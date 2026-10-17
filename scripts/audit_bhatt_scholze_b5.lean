import SerrePositivity.BhattScholze.Lemma103PerfectoidTensor
import SerrePositivity.BhattScholze.PerfectoidIdealLemma103
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

import SerrePositivity.BhattScholze.PerfectoidCompletedBaseChangeDiscrete
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedBaseChange_pure
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedBaseChangeSingleIso
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedBaseChange_pure
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedBaseChangeSingleIso
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.BhattScholze SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

-- The chosen single comparison is normalized on the actual H⁰, not an arbitrary module iso.
theorem audit_completedBaseChange_actual_H0_normalization
    (p : ℕ) [Fact p.Prime] (R S C : Type u)
    [CommRing R] [CommRing S] [CommRing C] [Algebra R S] [Algebra R C]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hC : IsIntegralPerfectoid C p) :
    let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
    (DerivedCategory.homologyFunctor (ModuleCat S) 0).map
        (integralPerfectoid_completedBaseChangeSingleIso p R S C hR hS hC).hom.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) 0).hom.app
        ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj X.obj) = 𝟙 _ := by
  have h := integralPerfectoid_completedBaseChange_pure p R S C hR hS hC
  letI := h.1
  letI := h.2
  exact normalizedPureHomologyIso_homology _ 0

-- For the original coefficient C=R all positive ordinary Tor tests over the new base vanish.
theorem audit_completedBaseChange_base_coefficient_positive_Tor
    (p : ℕ) [Fact p.Prime] (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R S)))
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (i : ℕ) (hi : 0 < i) :
    let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)))
    ∀ x : (((Tor (ModuleCat S) i).obj
      ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj X.obj)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj N)), x = 0 := by
  have hz : CategoryTheory.Limits.IsZero
      (((Tor (ModuleCat R) i).obj (ModuleCat.of R R)).obj N) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) R N j)
  have hs := (integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor
    p R S R hR hS hR hflat N k hN i 1).mp (hz.eq_of_src _ _)
  simpa only [map_one, one_smul] using hs

assert_no_sorry audit_completedBaseChange_actual_H0_normalization
assert_no_sorry audit_completedBaseChange_base_coefficient_positive_Tor
#print axioms audit_completedBaseChange_actual_H0_normalization
#print axioms audit_completedBaseChange_base_coefficient_positive_Tor

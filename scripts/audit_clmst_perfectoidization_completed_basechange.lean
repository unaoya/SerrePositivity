import SerrePositivity.BhattScholze.PerfectoidizationCompletedBaseChange
import SerrePositivity.BhattScholze.QuotientPerfectoidization
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsPerfectoidization.precomp_ringEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChangeMap
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChangeMap_left
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChangeMap_isPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChangeMap_exists_algEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChange_exists_linearEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectoidization_torCoefficientScalar_eq_zero_iff_baseChangedPerfectoidizationTor
#print axioms SerrePositivity.IsPerfectoidization.precomp_ringEquiv
#print axioms SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChangeMap
#print axioms SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChangeMap_left
#print axioms SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChangeMap_isPerfectoidization
#print axioms SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChangeMap_exists_algEquiv
#print axioms SerrePositivity.BhattScholze.perfectoidizationCompletedBaseChange_exists_linearEquiv
#print axioms SerrePositivity.BhattScholze.perfectoidization_torCoefficientScalar_eq_zero_iff_baseChangedPerfectoidizationTor

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.BhattScholze SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

theorem audit_B3_actual_new_base_coefficient_module
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hS : IsIntegralPerfectoid S p) (b : R) :
    let Q := R ⧸ Ideal.span {b}
    let C := QuotientPerfectoidization R (Ideal.span {b}) p hR
    ∀ (D : Type u) [CommRing D] [Algebra S D] (g : S ⊗[R] Q →ₐ[S] D),
      IsPerfectoidization p g.toRingHom →
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
        ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
          ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))).obj ≃ₗ[S] D) := by
  dsimp only
  intro D _ _ g hg
  let Q := R ⧸ Ideal.span {b}
  let C := QuotientPerfectoidization R (Ideal.span {b}) p hR
  let f : Q →ₐ[R] C := IsScalarTower.toAlgHom R Q C
  have hf : IsPerfectoidization p f.toRingHom :=
    isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {b}) p hR
  exact perfectoidizationCompletedBaseChange_exists_linearEquiv R p S Q C hR hS f hf D g hg

theorem audit_original_baseChanged_perfectoidization_kernel
    (R S A C D : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R A] [Algebra R C] [Algebra S D]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (g : S ⊗[R] A →ₐ[S] D) (hg : IsPerfectoidization p g.toRingHom) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S C)
    ∀ x : S ⊗[R] A,
      perfectoidizationCompletedBaseChangeMap R p S A C f x = 0 ↔ g x = 0 := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S C)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S C)
  letI := completedTensorH0LeftAlgebra R (p : R) S C
  obtain ⟨e, he⟩ := perfectoidizationCompletedBaseChangeMap_exists_algEquiv R p S A C
    hR hS f hf D g hg
  intro x
  have hx := RingHom.congr_fun he x
  constructor
  · intro h
    change e (perfectoidizationCompletedBaseChangeMap R p S A C f x) = g x at hx
    rw [h, map_zero] at hx
    exact hx.symm
  · intro h
    apply e.injective
    change e (perfectoidizationCompletedBaseChangeMap R p S A C f x) = e 0
    rw [map_zero]
    exact hx.trans h

assert_no_sorry audit_B3_actual_new_base_coefficient_module
assert_no_sorry audit_original_baseChanged_perfectoidization_kernel
#print axioms audit_B3_actual_new_base_coefficient_module
#print axioms audit_original_baseChanged_perfectoidization_kernel

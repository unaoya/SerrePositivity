import SerrePositivity.BhattScholze.CompletedBaseChangeCoefficientComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_left
assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_exists_algEquiv
assert_no_sorry SerrePositivity.BhattScholze.completedBaseChangeH0_exists_linearEquiv_perfectoidization
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_torCoefficientScalar_eq_zero_iff_selectedPerfectoidizationTor
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_left
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_exists_algEquiv
#print axioms SerrePositivity.BhattScholze.completedBaseChangeH0_exists_linearEquiv_perfectoidization
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_torCoefficientScalar_eq_zero_iff_selectedPerfectoidizationTor

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p)
include hR hS hT

theorem audit_selected_coefficient_original_ideal
    (D : Type u) [CommRing D] [Algebra S D] (f : S ⊗[R] T →ₐ[S] D)
    (hf : IsPerfectoidization p f.toRingHom) (J : Ideal S) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := completedTensorH0LeftAlgebra R (p : R) S T
    ∃ e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃ₐ[S] D,
      ∀ s ∈ J, e (completedTensorH0LeftAlgHom R (p : R) S T s) = algebraMap S D s := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := completedTensorH0LeftAlgebra R (p : R) S T
  obtain ⟨e, _⟩ := completedTensorPerfectoidizationMap_exists_algEquiv R p S T hR hS hT D f hf
  exact ⟨e, fun s _ => e.commutes s⟩

theorem audit_two_selected_perfectoidization_Tor
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R S)))
    (D₁ D₂ : Type u) [CommRing D₁] [CommRing D₂] [Algebra S D₁] [Algebra S D₂]
    (f₁ : S ⊗[R] T →ₐ[S] D₁) (f₂ : S ⊗[R] T →ₐ[S] D₂)
    (hf₁ : IsPerfectoidization p f₁.toRingHom) (hf₂ : IsPerfectoidization p f₂.toRingHom)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (i : ℕ) (s : R) :
    (∀ x : (((Tor (ModuleCat S) i).obj (ModuleCat.of S D₁)).obj
      ((ModuleCat.extendScalars (algebraMap R S)).obj N)), algebraMap R S s • x = 0) ↔
    (∀ x : (((Tor (ModuleCat S) i).obj (ModuleCat.of S D₂)).obj
      ((ModuleCat.extendScalars (algebraMap R S)).obj N)), algebraMap R S s • x = 0) := by
  exact (integralPerfectoid_torCoefficientScalar_eq_zero_iff_selectedPerfectoidizationTor
    R p S T hR hS hT hflat D₁ f₁ hf₁ N k hN i s).symm.trans
      (integralPerfectoid_torCoefficientScalar_eq_zero_iff_selectedPerfectoidizationTor
        R p S T hR hS hT hflat D₂ f₂ hf₂ N k hN i s)

assert_no_sorry audit_selected_coefficient_original_ideal
assert_no_sorry audit_two_selected_perfectoidization_Tor
#print axioms audit_selected_coefficient_original_ideal
#print axioms audit_two_selected_perfectoidization_Tor

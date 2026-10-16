import SerrePositivity.BhattScholze.CompletedTensorPerfectoidization
import SerrePositivity.BhattScholze.QuotientPerfectoidization
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap
assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_apply
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_apply
assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_isPerfectoidization
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_isPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_exists_equiv
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_exists_equiv
assert_no_sorry SerrePositivity.BhattScholze.completedTensorBaseChangeMap_isPerfectoidization
#print axioms SerrePositivity.BhattScholze.completedTensorBaseChangeMap_isPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_modP_bijective
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidizationMap_modP_bijective

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.BhattScholze SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard

-- Apply the actual base-change theorem to the original B3 choice, without B-I or Andre.
theorem audit_completed_tensor_B3_quotient_baseChange
    (R T : Type u) [CommRing R] [CommRing T] [Algebra R T]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hT : IsIntegralPerfectoid T p) (g : R) :
    let C := QuotientPerfectoidization R (Ideal.span {g}) p hR
    let X := boundedAboveCompletedTensorAlgebra R (p : R) C T
    let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.X.obj
    letI := derivedH0CommRing X
    ∃ F : (R ⧸ Ideal.span {g}) ⊗[R] T →+* H,
      IsPerfectoidization p F ∧ ∀ q t,
        F (q ⊗ₜ[R] t) = completedTensorPerfectoidizationMap R p C T
          (toQuotientPerfectoidization R (Ideal.span {g}) p hR q ⊗ₜ[R] t) := by
  dsimp only
  let Q := R ⧸ Ideal.span {g}
  let C := QuotientPerfectoidization R (Ideal.span {g}) p hR
  let X := boundedAboveCompletedTensorAlgebra R (p : R) C T
  letI := derivedH0CommRing X
  let f : Q →ₐ[R] C := IsScalarTower.toAlgHom R Q C
  have hf : IsPerfectoidization p f.toRingHom :=
    isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR
  refine ⟨perfectoidizationTensorBaseChangeMap f (completedTensorPerfectoidizationMap R p C T),
    completedTensorBaseChangeMap_isPerfectoidization R p C T hR hT Q f hf, ?_⟩
  intro q t
  rfl

-- Equality of the original kernels is obtained through the specified unit square.
theorem audit_completed_tensor_original_kernel
    (R S T D : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing D]
    [Algebra R S] [Algebra R T] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) (f : S ⊗[R] T →+* D)
    (hf : IsPerfectoidization p f) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    ∀ x : S ⊗[R] T, completedTensorPerfectoidizationMap R p S T x = 0 ↔ f x = 0 := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  obtain ⟨e, he⟩ := completedTensorPerfectoidizationMap_exists_equiv R p S T hR hS hT D f hf
  intro x
  have hx : e (completedTensorPerfectoidizationMap R p S T x) = f x :=
    RingHom.congr_fun he x
  constructor
  · intro h
    rw [← hx, h, map_zero]
  · intro h
    apply e.injective
    rw [hx, h, map_zero]

assert_no_sorry audit_completed_tensor_B3_quotient_baseChange
assert_no_sorry audit_completed_tensor_original_kernel
#print axioms audit_completed_tensor_B3_quotient_baseChange
#print axioms audit_completed_tensor_original_kernel


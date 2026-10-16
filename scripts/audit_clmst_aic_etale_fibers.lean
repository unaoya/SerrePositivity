import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedFibers
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.of_surjective
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.quotient
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.localization
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.isAlgClosed
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.residue_isAlgClosed
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_residueFiber_exists_algEquiv
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.of_surjective
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.quotient
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.localization
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.isAlgClosed
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.residue_isAlgClosed
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_residueFiber_exists_algEquiv

noncomputable section
universe u
open SerrePositivity
open scoped TensorProduct

theorem audit_aic_quotient_compatible_roots
    (R : Type u) [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R) (I : Ideal R)
    (n : ℕ) (hn : 0 < n) (a : R ⧸ I) :
    ∃ ρ : ℕ → R ⧸ I, ρ 0 = a ∧ ∀ k, ρ (k + 1) ^ n = ρ k :=
  (hR.quotient I).exists_compatible_pow_roots hn a

theorem audit_actual_finite_etale_fiber_original_scalars
    (R : Type u) [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R) (m : Ideal R) [m.IsMaximal]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] :
    letI := Ideal.Quotient.field m
    ∃ r : ℕ, ∃ e : (R ⧸ m) ⊗[R] A ≃ₐ[R ⧸ m] (Fin r → R ⧸ m),
      ∀ x : R, e (algebraMap R ((R ⧸ m) ⊗[R] A) x) = fun _ => Ideal.Quotient.mk m x := by
  letI := Ideal.Quotient.field m
  obtain ⟨r, ⟨e⟩⟩ := hR.finiteEtale_residueFiber_exists_algEquiv m A
  refine ⟨r, e, ?_⟩
  intro x
  rw [IsScalarTower.algebraMap_apply R (R ⧸ m) ((R ⧸ m) ⊗[R] A)]
  exact e.commutes (algebraMap R (R ⧸ m) x)

theorem audit_aic_localized_etale_fiber
    (R : Type u) [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R) (g : R)
    (m : Ideal (Localization.Away g)) [m.IsMaximal]
    (A : Type u) [CommRing A] [Algebra (Localization.Away g) A]
    [Module.Finite (Localization.Away g) A] [Algebra.Etale (Localization.Away g) A] :
    letI := Ideal.Quotient.field m
    ∃ r : ℕ, Nonempty (((Localization.Away g) ⧸ m) ⊗[Localization.Away g] A ≃ₐ[
      (Localization.Away g) ⧸ m] (Fin r → (Localization.Away g) ⧸ m)) := by
  exact (hR.localization (Submonoid.powers g) (Localization.Away g)).finiteEtale_residueFiber_exists_algEquiv
    m A

assert_no_sorry audit_aic_localized_etale_fiber
#print axioms audit_aic_localized_etale_fiber
assert_no_sorry audit_aic_quotient_compatible_roots
assert_no_sorry audit_actual_finite_etale_fiber_original_scalars
#print axioms audit_aic_quotient_compatible_roots
#print axioms audit_actual_finite_etale_fiber_original_scalars

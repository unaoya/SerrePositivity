import SerrePositivity.CLMST.PerfectoidFinitePresentationCommonModel
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.isModuleComplete_principal_ideal
assert_no_sorry SerrePositivity.DerivedCompletion.isModuleComplete_finitePresentation_algebra_principal
assert_no_sorry SerrePositivity.CLMST.localizationSplitting_exists_derivedComplete_common_model
#print axioms SerrePositivity.DerivedCompletion.isModuleComplete_principal_ideal
#print axioms SerrePositivity.DerivedCompletion.isModuleComplete_finitePresentation_algebra_principal
#print axioms SerrePositivity.CLMST.localizationSplitting_exists_derivedComplete_common_model

noncomputable section
universe u
open SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.CLMST
open scoped TensorProduct

-- The source closed side uses the original finite presentation hypotheses,
-- without any regularity condition on d or on p.
theorem audit_source_principal_closed_side_complete
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (d : R) :
    IsModuleComplete A (p : A) (ModuleCat.of A (Ideal.span {algebraMap R A d})) ∧
      IsModuleComplete (A ⧸ Ideal.span {algebraMap R A d})
        (p : A ⧸ Ideal.span {algebraMap R A d})
        (ModuleCat.of (A ⧸ Ideal.span {algebraMap R A d})
          (A ⧸ Ideal.span {algebraMap R A d})) := by
  let := Module.FinitePresentation.of_finite_of_finitePresentation R A
  have h := isModuleComplete_finitePresentation_algebra_principal R A
    (p : R) (algebraMap R A d) (hR.isModuleComplete R p)
  simpa only [map_natCast] using h.2.2

-- The same source calculation applies to the actual finite free product,
-- including rank zero, with its intrinsic ring and quotient scalar actions.
theorem audit_finite_product_principal_closed_side_complete
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (d : R) (r : ℕ) :
    IsModuleComplete (Fin r → R) (p : Fin r → R)
      (ModuleCat.of (Fin r → R) (Ideal.span {algebraMap R (Fin r → R) d})) ∧
      IsModuleComplete ((Fin r → R) ⧸ Ideal.span {algebraMap R (Fin r → R) d})
        (p : (Fin r → R) ⧸ Ideal.span {algebraMap R (Fin r → R) d})
        (ModuleCat.of ((Fin r → R) ⧸ Ideal.span {algebraMap R (Fin r → R) d})
          ((Fin r → R) ⧸ Ideal.span {algebraMap R (Fin r → R) d})) :=
  audit_source_principal_closed_side_complete R (Fin r → R) p hR d

-- The closed ideal on the actual model is precisely the image of the
-- original source ideal under u, rather than an unrelated chosen ideal.
theorem audit_actual_common_model_closed_ideal
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (Ideal.span {algebraMap R A d}).map u.toRingHom = Ideal.span {algebraMap R E d} ∧
        (Ideal.span {algebraMap R (Fin r → R) d}).map v.toRingHom =
          Ideal.span {algebraMap R E d} ∧
        IsModuleComplete E (p : E) (ModuleCat.of E (Ideal.span {algebraMap R E d})) := by
  obtain ⟨E, hE, aE, _hfinite, _hfp, _hmfp, _hcR, _hcE, hcI, _hcQ, u, v, _w, _⟩ :=
    localizationSplitting_exists_derivedComplete_common_model p hR d L r e
  refine ⟨E, hE, aE, u, v, ?_, ?_, hcI⟩
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {u (algebraMap R A d)} = _
    rw [u.commutes]
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {v (algebraMap R (Fin r → R) d)} = _
    rw [v.commutes]

assert_no_sorry audit_source_principal_closed_side_complete
assert_no_sorry audit_actual_common_model_closed_ideal
#print axioms audit_source_principal_closed_side_complete
#print axioms audit_actual_common_model_closed_ideal

assert_no_sorry audit_finite_product_principal_closed_side_complete
#print axioms audit_finite_product_principal_closed_side_complete

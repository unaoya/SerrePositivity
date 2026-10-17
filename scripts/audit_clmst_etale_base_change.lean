import SerrePositivity.CommutativeAlgebra.EtaleAwayBaseChange
import SerrePositivity.CLMST.PerfectoidEtaleCommonCover
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.etaleAway_tensor_baseChange
#print axioms SerrePositivity.etaleAway_tensor_baseChange

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST SerrePositivity.DerivedCompletion
open scoped TensorProduct

-- An arbitrary base change to an AIC perfectoid ring admits the actual cover
-- and finite presentation complete models. No ordinary flatness is installed.
theorem audit_baseChanged_actual_complete_cover
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hB : IsIntegralPerfectoid B p)
    (hAIC : IsAbsolutelyIntegrallyClosed B) (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away (algebraMap R B g)),
        Ideal.span (t : Set (Localization.Away (algebraMap R B g))) = ⊤ ∧
        ∀ q ∈ t, ∃ (r : ℕ) (M : Type u) (_ : CommRing M) (_ : Algebra B M),
          Module.Finite B M ∧ Module.FinitePresentation B M ∧
          IsModuleComplete B (p : B) (ModuleCat.of B M) ∧
          ∃ (u : (B ⊗[R] A) →ₐ[B] M) (v : (Fin r → B) →ₐ[B] M),
            u.toRingHom.Finite ∧ v.toRingHom.Finite := by
  let := GenericEtale.awayAlgebra R A g
  intro hetale
  have ht := etaleAway_tensor_baseChange (B := B) g hetale
  let := GenericEtale.awayAlgebra B (B ⊗[R] A) (algebraMap R B g)
  obtain ⟨t, hcover, _hpow, hmodels⟩ :=
    aic_finiteEtaleAway_exists_derivedComplete_common_cover (A := B ⊗[R] A)
      p hB hAIC (algebraMap R B g) ht
  refine ⟨t, hcover, ?_⟩
  intro q hq
  obtain ⟨r, _e, M, hM, aM, hfinite, _hfp, hmfp, hcB, _hcM, _hcI, _hcQ,
    u, v, _w, _hu, _hv, _hloc, huF, hvF, _⟩ := hmodels q hq
  exact ⟨r, M, hM, aM, hfinite, hmfp, hcB, u, v, huF, hvF⟩

assert_no_sorry audit_baseChanged_actual_complete_cover
#print axioms audit_baseChanged_actual_complete_cover

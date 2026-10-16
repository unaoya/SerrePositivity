import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtale
import Mathlib.RingTheory.Etale.Pi
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.localLinearMap_bijective_of_residue_bijective
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_local_exists_algEquiv
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_localized_exists_algEquiv
#print axioms SerrePositivity.localLinearMap_bijective_of_residue_bijective
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_local_exists_algEquiv
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_localized_exists_algEquiv

noncomputable section
universe u
open SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

theorem audit_aic_localized_etale_original_scalars
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r : ℕ, ∃ e : (Localization.AtPrime p) ⊗[R] A ≃ₐ[Localization.AtPrime p]
      (Fin r → Localization.AtPrime p),
      ∀ x : R, e (algebraMap R ((Localization.AtPrime p) ⊗[R] A) x) =
        fun _ => algebraMap R (Localization.AtPrime p) x := by
  obtain ⟨r, ⟨e⟩⟩ := hR.finiteEtale_localized_exists_algEquiv (A := A) p
  refine ⟨r, e, ?_⟩
  intro x
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
    ((Localization.AtPrime p) ⊗[R] A)]
  exact e.commutes (algebraMap R (Localization.AtPrime p) x)

theorem audit_aic_local_zero_etale_rank
    (R : Type u) [CommRing R] [IsLocalRing R] (hR : IsAbsolutelyIntegrallyClosed R) :
    ∃ r : ℕ, ∃ e : (Fin 0 → R) ≃ₐ[R] (Fin r → R), r = 0 := by
  obtain ⟨r, ⟨e⟩⟩ := hR.finiteEtale_local_exists_algEquiv (A := Fin 0 → R)
  refine ⟨r, e, ?_⟩
  by_contra hr
  have h01 : (0 : Fin r → R) = 1 := by
    rw [← e.map_zero, ← e.map_one]
    exact congrArg e (Subsingleton.elim (0 : Fin 0 → R) 1)
  exact zero_ne_one (congrFun h01 ⟨0, Nat.pos_of_ne_zero hr⟩)

assert_no_sorry audit_aic_localized_etale_original_scalars
assert_no_sorry audit_aic_local_zero_etale_rank
#print axioms audit_aic_localized_etale_original_scalars
#print axioms audit_aic_local_zero_etale_rank

import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtale
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.finiteAlgebra_exists_away_lift
assert_no_sorry SerrePositivity.finiteAlgebra_exists_away_lift_pi
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_exists_principal_comparison
#print axioms SerrePositivity.finiteAlgebra_exists_away_lift
#print axioms SerrePositivity.finiteAlgebra_exists_away_lift_pi
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_exists_principal_comparison

noncomputable section
universe u
open SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

-- The principal map retains the actual stalk splitting and original base scalars.
theorem audit_principal_etale_comparison_scalar_diagram
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R)
    (p : Ideal R) [p.IsPrime] :
    ∃ (r : ℕ) (d : R) (hd : d ∉ p) (ψ : A →ₐ[R] (Fin r → Localization.Away d))
      (e : (Localization.AtPrime p) ⊗[R] A ≃ₐ[Localization.AtPrime p]
        (Fin r → Localization.AtPrime p)),
      (∀ a i, IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R (Localization.AtPrime p))
        (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨d, hd⟩) (ψ a i) =
          e ((1 : Localization.AtPrime p) ⊗ₜ[R] a) i) ∧
      ∀ x : R, ψ (algebraMap R A x) = fun _ => algebraMap R (Localization.Away d) x := by
  obtain ⟨r, d, hd, ψ, e, hψ⟩ := hR.finiteEtale_exists_principal_comparison (A := A) p
  exact ⟨r, d, hd, ψ, e, hψ, fun x => ψ.commutes x⟩

-- Localizing at zero is included; no nonzero-denominator premise is hidden in the lift.
theorem audit_algebra_lift_zero_localization (R : Type u) [CommRing R] :
    ∃ (d : R) (hd : d ∈ Submonoid.powers (0 : R)) (ψ : R →ₐ[R] Localization.Away d),
      (IsLocalization.Away.liftAlgHom d
        (f := Algebra.ofId R (Localization.Away (0 : R)))
        (IsLocalization.map_units (Localization.Away (0 : R)) ⟨d, hd⟩)).comp ψ =
          Algebra.ofId R (Localization.Away (0 : R)) := by
  exact finiteAlgebra_exists_away_lift (Submonoid.powers (0 : R))
    (Localization.Away (0 : R)) (Algebra.ofId R (Localization.Away (0 : R)))

assert_no_sorry audit_principal_etale_comparison_scalar_diagram
assert_no_sorry audit_algebra_lift_zero_localization
#print axioms audit_principal_etale_comparison_scalar_diagram
#print axioms audit_algebra_lift_zero_localization

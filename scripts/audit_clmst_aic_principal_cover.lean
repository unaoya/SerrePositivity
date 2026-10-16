import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtaleCover
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.principalAlgebraComparison_exists_algEquiv
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_exists_principal_algEquiv
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_principalSplitting_span_eq_top
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_exists_finite_principal_cover
#print axioms SerrePositivity.principalAlgebraComparison_exists_algEquiv
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_exists_principal_algEquiv
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_principalSplitting_span_eq_top
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtale_exists_finite_principal_cover

noncomputable section
universe u
open SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

theorem audit_aic_finite_cover_original_scalars
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R) :
    ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧ ∀ g ∈ t,
      ∃ r : ℕ, ∃ e : (Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
        (Fin r → Localization.Away g),
        ∀ x : R, e (algebraMap R ((Localization.Away g) ⊗[R] A) x) =
          fun _ => algebraMap R (Localization.Away g) x := by
  obtain ⟨t, ht, hsplit⟩ := hR.finiteEtale_exists_finite_principal_cover (A := A)
  refine ⟨t, ht, ?_⟩
  intro g hg
  obtain ⟨r, ⟨e⟩⟩ := hsplit g hg
  refine ⟨r, e, ?_⟩
  intro x
  rw [IsScalarTower.algebraMap_apply R (Localization.Away g) ((Localization.Away g) ⊗[R] A)]
  exact e.commutes (algebraMap R (Localization.Away g) x)

theorem audit_principal_shrink_original_multiplication
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FinitePresentation R A] (p : Ideal R) [p.IsPrime]
    (d : R) (hd : d ∉ p) (r : ℕ) (ψ : A →ₐ[R] (Fin r → Localization.Away d))
    (e : (Localization.AtPrime p) ⊗[R] A ≃ₐ[Localization.AtPrime p]
      (Fin r → Localization.AtPrime p))
    (hψ : ∀ a i, IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R (Localization.AtPrime p))
      (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨d, hd⟩)
        (ψ a i) = e ((1 : Localization.AtPrime p) ⊗ₜ[R] a) i) :
    ∃ (g : R) (_ : g ∉ p) (hdg : d ∣ g)
      (E : (Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
        (Fin r → Localization.Away g)),
      ∀ a b i, E ((1 : Localization.Away g) ⊗ₜ[R] (a * b)) i =
        IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R (Localization.Away g))
          (isUnit_of_dvd_unit (map_dvd (algebraMap R (Localization.Away g)) hdg)
            (IsLocalization.Away.algebraMap_isUnit g)) (ψ a i * ψ b i) := by
  obtain ⟨g, hg, hdg, E, hE⟩ := principalAlgebraComparison_exists_algEquiv p d hd r ψ e hψ
  refine ⟨g, hg, hdg, E, ?_⟩
  intro a b i
  rw [hE]
  exact congrArg _ (congrFun (ψ.map_mul a b) i)

assert_no_sorry audit_aic_finite_cover_original_scalars
assert_no_sorry audit_principal_shrink_original_multiplication
#print axioms audit_aic_finite_cover_original_scalars
#print axioms audit_principal_shrink_original_multiplication

import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtaleIntegralCover
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.principalLocalizationTower_algebraMap
assert_no_sorry SerrePositivity.principalLocalizationTower_scalarTower
assert_no_sorry SerrePositivity.principalLocalizationTower_isLocalization
assert_no_sorry SerrePositivity.principalLocalizationTowerEquiv
assert_no_sorry SerrePositivity.originalAwayTensorEquiv
assert_no_sorry SerrePositivity.originalAwayTensorEquiv_tmul
assert_no_sorry SerrePositivity.doubleLocalizationTensorEquiv
assert_no_sorry SerrePositivity.doubleLocalizationTensorEquiv_tmul
assert_no_sorry SerrePositivity.localizationSplitting_exists_finite_common_model
assert_no_sorry SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_integral_cover
#print axioms SerrePositivity.principalLocalizationTower_algebraMap
#print axioms SerrePositivity.principalLocalizationTower_scalarTower
#print axioms SerrePositivity.principalLocalizationTower_isLocalization
#print axioms SerrePositivity.principalLocalizationTowerEquiv
#print axioms SerrePositivity.originalAwayTensorEquiv
#print axioms SerrePositivity.originalAwayTensorEquiv_tmul
#print axioms SerrePositivity.doubleLocalizationTensorEquiv
#print axioms SerrePositivity.doubleLocalizationTensorEquiv_tmul
#print axioms SerrePositivity.localizationSplitting_exists_finite_common_model
#print axioms SerrePositivity.IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_integral_cover

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open SerrePositivity
open scoped TensorProduct

-- The actual finite étale hypothesis off g gives integral maps over the original R.
theorem audit_actual_integral_cover_original_scalars
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (hR : IsAbsolutelyIntegrallyClosed R) (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away g),
        Ideal.span (t : Set (Localization.Away g)) = ⊤ ∧
        (∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun f : t =>
          g * (IsLocalization.Away.sec g f.1).1))) ∧
        ∀ f ∈ t, ∃ (r : ℕ) (E : Subalgebra R (Fin r → Localization.Away f)),
          Module.Finite R E ∧
          IsLocalizedModule (.powers (g * (IsLocalization.Away.sec g f).1)) E.val.toLinearMap ∧
          ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
            @RingHom.IsIntegral A E inferInstance inferInstance u.toRingHom ∧
            @RingHom.IsIntegral (Fin r → R) E inferInstance inferInstance v.toRingHom ∧
            ∀ x : R, E.val (u (algebraMap R A x)) =
              E.val (v (algebraMap R (Fin r → R) x)) := by
  letI := GenericEtale.awayAlgebra R A g
  intro he
  obtain ⟨t, ht, hcover, hmodels⟩ := hR.finiteEtaleAway_exists_finite_integral_cover g he
  refine ⟨t, ht, hcover, ?_⟩
  intro f hf
  obtain ⟨r, _e, E, hfinite, hloc, u, v, _hu, _hv, huF, hvF⟩ := hmodels f hf
  refine ⟨r, E, hfinite, hloc, u, v, huF.to_isIntegral, hvF.to_isIntegral, ?_⟩
  intro x
  rw [u.commutes, v.commutes]

-- Inverting a zero cover member still normalizes correctly, without a Nontrivial assumption.
theorem audit_zero_cover_member_normalization
    (R : Type u) [CommRing R] (g : R) :
    Subsingleton (Localization.Away
      (g * (IsLocalization.Away.sec g (0 : Localization.Away g)).1)) := by
  let U := Localization.Away (0 : Localization.Away g)
  have hzero : IsUnit (0 : U) := by
    simpa only [map_zero] using
      (IsLocalization.Away.algebraMap_isUnit (S := U) (0 : Localization.Away g))
  let : Subsingleton U := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hzero)
  let e := principalLocalizationTowerEquiv g (0 : Localization.Away g)
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

assert_no_sorry audit_actual_integral_cover_original_scalars
assert_no_sorry audit_zero_cover_member_normalization
#print axioms audit_actual_integral_cover_original_scalars
#print axioms audit_zero_cover_member_normalization

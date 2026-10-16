module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtaleAwayCover
public import SerrePositivity.CommutativeAlgebra.DoubleLocalizationTensorComparison
public import SerrePositivity.CommutativeAlgebra.FiniteCommonLocalizationModel

/-! # Finite integral comparison models on the actual splitting cover off g

Each model is finite over the original R and retains the actual splitting map of A.
Its embedding localizes at g times the chosen original numerator of the cover member.
No almost invariance after perfectoidization is asserted here.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct

/-- The actual finite splitting cover off g has finite integral comparison models
over the original R, not merely over the localized base. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_integral_cover
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (hR : IsAbsolutelyIntegrallyClosed R) (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away g),
        Ideal.span (t : Set (Localization.Away g)) = ⊤ ∧
        (∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun f : t =>
          g * (IsLocalization.Away.sec g f.1).1))) ∧
        ∀ f ∈ t, ∃ (r : ℕ)
          (e : (Localization.Away f) ⊗[Localization.Away g]
            (Localization.Away (algebraMap R A g)) ≃ₐ[Localization.Away f]
              (Fin r → Localization.Away f))
          (E : Subalgebra R (Fin r → Localization.Away f)),
          Module.Finite R E ∧
          IsLocalizedModule (.powers (g * (IsLocalization.Away.sec g f).1)) E.val.toLinearMap ∧
          ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
            (∀ a, E.val (u a) = e ((1 : Localization.Away f) ⊗ₜ[Localization.Away g]
              algebraMap A (Localization.Away (algebraMap R A g)) a)) ∧
            (∀ b i, E.val (v b) i = algebraMap R (Localization.Away f) (b i)) ∧
            u.toRingHom.Finite ∧ v.toRingHom.Finite := by
  letI := GenericEtale.awayAlgebra R A g
  intro hetale
  obtain ⟨t, ht, hsplit, hcover⟩ := hR.finiteEtaleAway_exists_finite_cover g hetale
  refine ⟨t, ht, hcover, ?_⟩
  intro f hf
  obtain ⟨r, ⟨e⟩⟩ := hsplit f hf
  let d := g * (IsLocalization.Away.sec g f).1
  letI : IsLocalization (.powers d) (Localization.Away f) :=
    principalLocalizationTower_isLocalization g f
  let e' := (doubleLocalizationTensorEquiv R A g f).trans e
  obtain ⟨E, hfinite, hloc, u, v, hu, hv, huF, hvF⟩ :=
    localizationSplitting_exists_finite_common_model (.powers d) (Localization.Away f) r e'
  refine ⟨r, e, E, hfinite, hloc, u, v, ?_, hv, huF, hvF⟩
  intro a
  rw [hu]
  change e (doubleLocalizationTensorEquiv R A g f ((1 : Localization.Away f) ⊗ₜ[R] a)) = _
  rw [doubleLocalizationTensorEquiv_tmul]

end SerrePositivity

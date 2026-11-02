module

public import SerrePositivity.BhattScholze.Perfectoidization.FiniteComparisonExcision
public import SerrePositivity.CLMST.RPerfdTorBaseChange
public import SerrePositivity.CLMST.StageRPerfd

/-! # Both original KL cohomology conclusions from the explicit excision input

The same chosen RPerfd, stage maps and original scalar ideal are retained.
Finite comparison excision remains an unproved hypothesis; Corollary 4.0.4 is
not invoked and its existing citation is not replaced by this conditional theorem.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory Section2 IsLocalRing
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard

/-- The full original low local-cohomology and all finite-stage Koszul
conclusions follow from excision on AIC perfectoid extensions of the completed
tower. No Tor-zero hypothesis is supplied by the caller. -/
theorem rPerfd_cohomology_vanishing_of_finiteComparison_excision
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {h : ℕ} (t : Fin h → A)
    (D : Type u) [CommRing D] [Algebra A D] [Module.Finite A D]
    [IsLocalRing D] [IsNoetherianRing D]
    (p : ℕ) [Fact p.Prime] (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hetale : letI := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (hExcision : ∀ (E : Type u) [CommRing E] [Algebra (CompletedTower A t p) E],
      IsIntegralPerfectoid E p → IsAbsolutelyIntegrallyClosed E → BhattScholze.KLFiniteComparisonExcision E p) :
    (∀ i : ℕ, i < h →
      ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i
          (RPerfd A D t p hperf)
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin h → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom
            (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
          perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p)
                (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)) := by
  let : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D
  let : Algebra.FinitePresentation A D := inferInstance
  let f : ((CompletedTower A t p) ⊗[A] D) →ₐ[CompletedTower A t p]
      (RPerfd A D t p hperf) :=
    { toMixedPerfectoid A D t p hperf with commutes' := fun _ => rfl }
  have hf : IsPerfectoidization p f.toRingHom := isPerfectoidization_toMixedPerfectoid A D t p hperf
  let := GenericEtale.awayAlgebra A D g
  have he := etaleAway_tensor_baseChange (B := CompletedTower A t p) g hetale
  let := GenericEtale.awayAlgebra (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D)
    (algebraMap A (CompletedTower A t p) g)
  have hTor := BhattScholze.perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision
    p hperf hExcision (algebraMap A (CompletedTower A t p) g) f hf he
  exact rPerfd_cohomology_vanishing_of_tower_power_torsion A t D p hperf
    ht hdim hsop j₀ htp g (fun N k _hk hN i hi s hs => hTor N k hN i hi s hs)

end SerrePositivity.CLMST

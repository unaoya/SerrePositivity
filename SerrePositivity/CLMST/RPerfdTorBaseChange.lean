module

public import SerrePositivity.CLMST.RPerfdCohomologyInputs
public import SerrePositivity.BhattScholze.PerfectoidIdeal.CompletedQuotient
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.HomologicalAlgebra.PowerTorsionTorBaseChange
public import SerrePositivity.CLMST.StageRPerfd

/-! # Original completed-tower Tor tests supply the A-coefficient inputs

The completed tower is flat over the original regular local base. The existing
RPerfd, perfectoid ideal, scalar actions, and all finite-stage maps are retained.
The power-torsion input over the tower remains an explicit mathematical hypothesis.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory Section2 IsLocalRing
attribute [local instance] HasDerivedCategory.standard
variable (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {h : ℕ} (t : Fin h → A)
    (D : Type u) [CommRing D] [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

/-- The tower-side power-torsion Tor input gives the original A-side tests. -/
lemma rPerfd_power_torsion_tor_eq_zero_of_completedTower (g : A)
    (hTor : ∀ (L : ModuleCat.{u} (CompletedTower A t p)) (k : ℕ), 0 < k →
      (∀ x : L, (p : CompletedTower A t p) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0)
    (N : ModuleCat.{u} A) (k : ℕ) (hk : 0 < k)
    (hN : ∀ x : N, (p : A) ^ k • x = 0)
    (j : ℕ) (hj : 0 < j) (s : CompletedTower A t p)
    (hs : s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) :
    torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N j
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0 := by
  letI := flat_completedTower_over_base A t p
  exact powerTorsionTorInput_of_flat_baseChange (R := A) (B := CompletedTower A t p)
    (C := RPerfd A D t p hperf) p _ hTor N k hk hN j hj s hs

/-- Both Cor 4.0.4 conclusions from the original completed quotient product and
the original tower-side power-torsion tests. -/
lemma rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_tower_power_torsion
    [IsLocalRing D] [IsNoetherianRing D]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hμ : IsIso ((DerivedCompletion.derivedComplexCompletionFunctor
      (CompletedTower A t p) (p : CompletedTower A t p)).map
        (boundedAboveDerivedAlgebraMul (R := CompletedTower A t p)
          ((CompletedTower A t p) ⧸ perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g))).hom))
    (hTor : ∀ (L : ModuleCat.{u} (CompletedTower A t p)) (k : ℕ), 0 < k →
      (∀ x : L, (p : CompletedTower A t p) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
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
                (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)) :=
  rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_power_torsion
    A t D p hperf ht hdim hsop j₀ htp g hμ
    (rPerfd_power_torsion_tor_eq_zero_of_completedTower A t D p hperf g hTor)

/-- The actual quotient product is proved; only the original tower-side Tor tests remain explicit. -/
lemma rPerfd_cohomology_vanishing_of_tower_power_torsion
    [IsLocalRing D] [IsNoetherianRing D]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hTor : ∀ (L : ModuleCat.{u} (CompletedTower A t p)) (k : ℕ), 0 < k →
      (∀ x : L, (p : CompletedTower A t p) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
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
                (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)) :=
  rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_tower_power_torsion
    A t D p hperf ht hdim hsop j₀ htp g
    (BhattScholze.perfectoidIdeal_completedQuotientMul_map_isIso (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) hTor

end SerrePositivity.CLMST

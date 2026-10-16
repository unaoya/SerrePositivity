module

public import SerrePositivity.CLMST.ConditionalCohomologyVanishing
public import SerrePositivity.HomologicalAlgebra.TorFiniteCoefficients
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorAlgebraComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteTensorComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteCoefficientPowerComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerDerivedComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTorComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteCoefficientPowerHolim
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerHolimNaturality
public import SerrePositivity.CommutativeAlgebra.PerfectoidDerivedComplete
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdeal
public import SerrePositivity.CommutativeAlgebra.RegularParameters

/-! # Concrete inputs for the cohomology comparison on the selected RPerfd

The standard parameter resolutions and all finite-stage maps are supplied here.
Quotient-image idempotence and higher Tor annihilation remain separate inputs.
The original perfectoidization choice, coefficient actions, and stage maps are retained.
The selected RPerfd still depends on the existing integral-perfectoidization
existence input; this file does not remove that input or prove almost flatness.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory Section2 IsLocalRing
attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {h : ℕ} (t : Fin h → A)

/-- Every power of the actual regular parameter system resolves its quotient,
including power zero. No regularity of RPerfd is used. -/
lemma parameter_power_isKoszulResolution
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdim : ringKrullDim A = h) (k : ℕ) :
    IsKoszulResolution (fun j => t j ^ k) :=
  isKoszulResolution_all_powers t ht
    (isWeaklyRegular_of_span_eq_maximalIdeal A t ht hdim) k

variable (D : Type u) [CommRing D] [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

/-- The selected RPerfd is derived p-complete for its original A-action. This
uses its existing perfectoidization property, without a torsion-free assumption. -/
lemma rPerfd_isModuleComplete :
    DerivedCompletion.IsModuleComplete A (p : A)
      (ModuleCat.of A (RPerfd A D t p hperf)) :=
  IsIntegralPerfectoid.isModuleComplete_algebra A (RPerfd A D t p hperf) p
    (isPerfectoidization_toMixedPerfectoid A D t p hperf).1

/-- The actual RPerfd derived tensor with every finite A-module is complete.
No completeness, p-regularity, or flatness is imposed on the test module. -/
lemma rPerfd_derivedTensor_isComplete (N : ModuleCat.{u} A) [Module.Finite A N] :
    DerivedCompletion.IsComplete A (p : A)
      ((boundedAboveDerivedTensorModuleFunctor
        (ModuleCat.of A (RPerfd A D t p hperf))).obj N) :=
  DerivedCompletion.boundedAboveDerivedTensor_isComplete_of_finite_regular A (p : A)
    (ModuleCat.of A (RPerfd A D t p hperf)) N (rPerfd_isModuleComplete A t D p hperf)

/-- The original Koszul-completion-to-power-cokernel comparison is a
quasi-isomorphism in the actual RPerfd tensor model for every finite test module. -/
lemma rPerfd_finiteCoefficientPowerComparison_quasiIso
    (N : ModuleCat.{u} A) [Module.Finite A N] :
    QuasiIso (DerivedCompletion.koszulPowerCokernelComparison (p : A)
      (DerivedCompletion.finiteCoefficientTensorModel A
        (ModuleCat.of A (RPerfd A D t p hperf)) N)) :=
  DerivedCompletion.finiteCoefficientPowerComparison_quasiIso A (p : A)
    (ModuleCat.of A (RPerfd A D t p hperf)) N (rPerfd_isModuleComplete A t D p hperf)

/-- Each original power cokernel is the actual derived tensor of the selected
RPerfd with N/pⁿN. N need not be finite, flat, regular, or complete. -/
def rPerfd_modulePowerDerivedTensorIso (N : ModuleCat.{u} A) (n : ℕ) :
    DerivedCategory.Q.obj (DerivedCompletion.powerCokernelComplex (p : A)
      ((moduleTensorCochainFunctor (extRes (projectiveResolution
        (ModuleCat.of A (RPerfd A D t p hperf))))).obj N) n) ≅
      (boundedAboveDerivedTensorModuleFunctor (ModuleCat.of A (RPerfd A D t p hperf))).obj
        (DerivedCompletion.modulePowerReduction (p : A) N n) :=
  DerivedCompletion.modulePowerDerivedTensorIso (p : A)
    (ModuleCat.of A (RPerfd A D t p hperf)) N n

/-- The original finite-test tensor is the holim of the ordinary quotient tower.
The selected perfectoidization and original A-action are unchanged. -/
def rPerfd_finiteCoefficientPowerHolimIso (N : ModuleCat.{u} A) [Module.Finite A N] :
    (boundedAboveDerivedTensorModuleFunctor (ModuleCat.of A (RPerfd A D t p hperf))).obj N ≅
      DerivedCategory.Q.obj (DerivedCompletion.modulePowerDerivedTensorHolimComplex A (p : A)
        (ModuleCat.of A (RPerfd A D t p hperf)) N) :=
  DerivedCompletion.finiteCoefficientPowerHolimIso A (p : A)
    (ModuleCat.of A (RPerfd A D t p hperf)) N (rPerfd_isModuleComplete A t D p hperf)

/-- Finite-test algebra-valued Tor is derived p-complete over the original
completed tower, using its existing action on the same RPerfd. -/
lemma rPerfd_torAlgebra_isModuleComplete (N : ModuleCat.{u} A) [Module.Finite A N] (i : ℕ) :
    DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p)
      ((ModuleCat.restrictScalars
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
          (((ModuleCat.extendScalars (algebraMap A (RPerfd A D t p hperf))).leftDerived i).obj N)) :=
  DerivedCompletion.torAlgebra_isModuleComplete_restrict_of_finite
    (RPerfd A D t p hperf) N (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf)) p
    (rPerfd_isModuleComplete A t D p hperf) i

/-- The original almost-Tor input is the actual completed-tower annihilator
condition on algebra-valued Tor, for arbitrary test modules. -/
lemma rPerfd_torAlgebra_annihilator_iff (N : ModuleCat.{u} A) (i : ℕ) (g : A) :
    (∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g),
      torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) ↔
      (letI := Module.compHom
        (((ModuleCat.extendScalars (algebraMap A (RPerfd A D t p hperf))).leftDerived i).obj N)
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
       perfectoidIdeal (CompletedTower A t p) p hperf
         (algebraMap A (CompletedTower A t p) g) ≤ Module.annihilator (CompletedTower A t p)
           (((ModuleCat.extendScalars (algebraMap A (RPerfd A D t p hperf))).leftDerived i).obj N)) :=
  torAlgebraComparison_restricted_annihilator_iff (CompletedTower A t p)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g)) N i

/-- The actual finite-stage map has the base compatibility required by the
Koszul/local-cohomology theorem. -/
lemma toRPerfd_algebraMap_A (n : ℕ) (x : A) :
    toRPerfd A D t p hperf n
      (algebraMap D (StageAlgebra A D t p n) (algebraMap A D x)) =
        algebraMap A (RPerfd A D t p hperf) x := by
  rw [toRPerfd_algebraMap_D]
  exact (IsScalarTower.algebraMap_apply A D (RPerfd A D t p hperf) x).symm

/-- The distinguished p-coordinate agrees under the original completed-tower
action on RPerfd. -/
lemma rPerfd_p_coordinate (j₀ : Fin h) (htp : t j₀ = (p : A)) :
    algebraMap (CompletedTower A t p) (RPerfd A D t p hperf)
      (p : CompletedTower A t p) = algebraMap A (RPerfd A D t p hperf) (t j₀) := by
  simp only [htp, map_natCast]

/-- Supply the full Tor input from finitely generated tests on the same selected
RPerfd. No completeness assumption is imposed on the arbitrary test module. -/
lemma rPerfd_tor_eq_zero_of_finite (g : A)
    (hTor : ∀ (N : ModuleCat.{u} A), Module.Finite A N → ∀ (i : ℕ), 0 < i →
      ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0)
    (N : ModuleCat.{u} A) (i : ℕ) (hi : 0 < i)
    (s : CompletedTower A t p)
    (hs : s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g)) :
    torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0 :=
  torCoefficientScalarEndomorphism_eq_zero_of_finite (RPerfd A D t p hperf) i
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s)
    (fun M hM => hTor M hM i hi s hs) N

/-- Apply the common comparison to the selected RPerfd and the actual almost
ideal. The two remaining inputs are kept at their full original quantifiers. -/
lemma rPerfd_cohomology_vanishing_of_tor_idempotent
    [IsLocalRing D] [IsNoetherianRing D]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hI : ∀ k : ℕ, 0 < k → IsIdempotentElem
      ((perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)).map
          (Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p) ^ k}))))
    (hTor : ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N j
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
    (∀ i : ℕ, i < h →
      ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g),
        HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i
          (RPerfd A D t p hperf)
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) ∧
    (∀ n : ℕ,
      let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin h → StageAlgebra A D t p n),
        IsSystemOfParameters (StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom
            (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
          perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p)
                (koszulHomologySelf (fun j => toRPerfd A D t p hperf n (y j)) i)) := by
  exact conditional_corollary_4_0_4 t p hsop
    (parameter_power_isKoszulResolution A t ht hdim)
    (fun n => (toRPerfd A D t p hperf n).toRingHom)
    (toRPerfd_algebraMap_A A t D p hperf)
    (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g))
    (p : CompletedTower A t p) j₀ (rPerfd_p_coordinate A t D p hperf j₀ htp) hI hTor

end SerrePositivity.CLMST

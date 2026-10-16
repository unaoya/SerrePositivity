import SerrePositivity.CLMST.RPerfdTorBaseChange
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTorProduct
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTensorTorZero
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorMapZero
import SerrePositivity.CLMST.RPerfdCohomologyInputs
import Mathlib.Util.AssertNoSorry

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST SerrePositivity.Section2 IsLocalRing

assert_no_sorry parameter_power_isKoszulResolution
#print axioms parameter_power_isKoszulResolution
#print axioms toRPerfd_algebraMap_A
#print axioms rPerfd_p_coordinate
#print axioms rPerfd_tor_eq_zero_of_finite
#print axioms rPerfd_isModuleComplete
#print axioms rPerfd_derivedTensor_isComplete
#print axioms rPerfd_finiteCoefficientPowerComparison_quasiIso
#print axioms rPerfd_modulePowerDerivedTensorIso
#print axioms rPerfd_cohomology_vanishing_of_tor_idempotent

-- The original selected RPerfd has a known existence dependency. Reject all
-- other sorry declarations, including the cohomology and idempotence inputs.
meta section
open Lean Elab Command
private partial def checkRPerfdDependencies (todo : List Name) (visited : NameSet) :
    CoreM NameSet := do
  match todo with
  | [] => return visited
  | n :: todo =>
    if visited.contains n then return ← checkRPerfdDependencies todo visited
    if [ `SerrePositivity.CLMST.Inputs.corollary_4_0_4,
        `SerrePositivity.CLMST.Inputs.proposition_2_4_7,
        `SerrePositivity.CLMST.Inputs.perfectoidIdealMod_idempotent].contains n then
      throwError "Forbidden cohomology input: {n}"
    let visited := visited.insert n
    let some info := (← getEnv).find? n
      | return ← checkRPerfdDependencies todo visited
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral then
      throwError "Unapproved sorry in {n}"
    checkRPerfdDependencies (deps.toList ++ todo) visited

elab "assert_rperfd_cohomology_dependencies" : command => do
  let roots := [``rPerfd_cohomology_vanishing_of_tower_power_torsion, ``toRPerfd_algebraMap_A, ``rPerfd_p_coordinate,
    ``rPerfd_tor_eq_zero_of_finite, ``rPerfd_isModuleComplete,
    ``rPerfd_derivedTensor_isComplete, ``rPerfd_finiteCoefficientPowerComparison_quasiIso,
    ``rPerfd_modulePowerDerivedTensorIso, ``rPerfd_finiteCoefficientPowerHolimIso,
    ``rPerfd_torAlgebra_isModuleComplete, ``rPerfd_torAlgebra_annihilator_iff,
    ``rPerfd_torMilnor_endpoints_isModuleComplete, ``rPerfd_torMilnor_endpoints_annihilated,
    ``rPerfd_torMilnorShortComplex, ``rPerfd_torMilnorShortComplex_shortExact,
    ``rPerfd_tor_eq_zero_of_power_torsion_and_extensions,
    ``rPerfd_tor_eq_zero_of_power_torsion_and_quotientTorOne,
    ``rPerfd_tor_eq_zero_of_power_torsion_and_completed_quotient_mul,
    ``rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_power_torsion,
    ``rPerfd_power_torsion_tor_eq_zero_of_completedTower,
    ``rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_tower_power_torsion,
    ``rPerfd_cohomology_vanishing_of_tor_idempotent]
  let _ ← liftCoreM <| checkRPerfdDependencies roots {}
  logInfo "Only the existing integral-perfectoidization existence sorry is permitted."
end

assert_rperfd_cohomology_dependencies

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)

-- The zero-th power in the actual local-cohomology diagram is included.
example : IsKoszulResolution (fun j => t j ^ (0 : ℕ)) :=
  parameter_power_isKoszulResolution A t ht hdim 0

-- No positivity hypothesis on the number of parameters was added.
example (t₀ : Fin 0 → A) (ht₀ : Ideal.span (Set.range t₀) = maximalIdeal A)
    (hdim₀ : ringKrullDim A = 0) (k : ℕ) :
    IsKoszulResolution (fun j => t₀ j ^ k) :=
  parameter_power_isKoszulResolution A t₀ ht₀ hdim₀ k

variable (D : Type u) [CommRing D] [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

-- All finite stages, including zero, retain their original D-algebra action.
example (n : ℕ) (x : A) :
    toRPerfd A D t p hperf n
      (algebraMap D (StageAlgebra A D t p n) (algebraMap A D x)) =
        algebraMap A (RPerfd A D t p hperf) x :=
  toRPerfd_algebraMap_A A t D p hperf n x

open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
local notation "C₀" => ModuleCat.of A (RPerfd A D t p hperf)
local notation "K₀" => extRes (projectiveResolution C₀)

private lemma rperfd_power_stage_quotient_map (N : ModuleCat.{u} A) (n : ℕ) :
    DerivedCategory.Q.map (cokernel.π
      (smulId ((p : A) ^ n) ((moduleTensorCochainFunctor K₀).obj N))) ≫
        (rPerfd_modulePowerDerivedTensorIso A t D p hperf N n).hom =
      (derivedTensorCoefficientModelIso C₀ N).inv ≫
        (boundedAboveDerivedTensorModuleFunctor C₀).map (modulePowerReductionMap (p : A) N n) :=
  modulePowerDerivedTensorIso_π (p : A) C₀ N n

private lemma rperfd_power_stage_transition (N : ModuleCat.{u} A) (n : ℕ) :
    DerivedCategory.Q.map (powerCokernelComplexTransition (p : A)
      ((moduleTensorCochainFunctor K₀).obj N) n) ≫
        (rPerfd_modulePowerDerivedTensorIso A t D p hperf N n).hom =
      (rPerfd_modulePowerDerivedTensorIso A t D p hperf N (n + 1)).hom ≫
        (boundedAboveDerivedTensorModuleFunctor C₀).map (modulePowerReductionTransition (p : A) N n) :=
  modulePowerDerivedTensorIso_transition (p : A) C₀ N n

private lemma rperfd_power_stage_scalar (N : ModuleCat.{u} A) (n : ℕ)
    (c : RPerfd A D t p hperf) :
    let f : C₀ ⟶ C₀ := ModuleCat.ofHom (LinearMap.mulLeft A c)
    DerivedCategory.Q.map (modulePowerTensorCokernelMap (p : A) N
      (extLift (projectiveResolution C₀) f (projectiveResolution C₀)) n) ≫
        (rPerfd_modulePowerDerivedTensorIso A t D p hperf N n).hom =
      (rPerfd_modulePowerDerivedTensorIso A t D p hperf N n).hom ≫
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map f)
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (modulePowerReduction (p : A) N n))))).hom :=
  modulePowerDerivedTensorIso_naturality (p : A) N
    (ModuleCat.ofHom (LinearMap.mulLeft A c)) n

private lemma rperfd_power_stage_tor_scalar (N : ModuleCat.{u} A) (n i : ℕ)
    (c : RPerfd A D t p hperf) :
    HomologicalComplex.homologyMap (modulePowerTensorCokernelMap (p : A) N
      (extLift (projectiveResolution C₀) (ModuleCat.ofHom (LinearMap.mulLeft A c))
        (projectiveResolution C₀)) n) (-(i : ℤ)) = 0 ↔
      torCoefficientScalarEndomorphism (RPerfd A D t p hperf)
        (modulePowerReduction (p : A) N n) i c = 0 :=
  modulePowerCokernelTorIso_scalar_zero_iff (p : A) N (RPerfd A D t p hperf) n i c

private lemma rperfd_power_stage_torsion_input (N : ModuleCat.{u} A) (i : ℕ)
    (c : RPerfd A D t p hperf)
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) →
        torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L i c = 0) (n : ℕ) :
    HomologicalComplex.homologyMap (modulePowerTensorCokernelMap (p : A) N
      (extLift (projectiveResolution C₀) (ModuleCat.ofHom (LinearMap.mulLeft A c))
        (projectiveResolution C₀)) n) (-(i : ℤ)) = 0 :=
  modulePowerCokernel_scalar_zero_of_power_torsion_tests (p : A) N
    (RPerfd A D t p hperf) i c hTor n

meta section
open Lean Elab Command
elab "assert_rperfd_power_stage_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_power_stage_quotient_map,
    ``rperfd_power_stage_transition, ``rperfd_power_stage_scalar,
    ``rperfd_power_stage_tor_scalar, ``rperfd_power_stage_torsion_input] {}
  logInfo "Actual RPerfd power stages: quotient, transition, derived scalar and standard Tor actions checked."
end

assert_rperfd_power_stage_dependencies
#print axioms rperfd_power_stage_quotient_map
#print axioms rperfd_power_stage_transition
#print axioms rperfd_power_stage_scalar
#print axioms rperfd_power_stage_tor_scalar
#print axioms rperfd_power_stage_torsion_input

private lemma rperfd_power_holim_projection (N : ModuleCat.{u} A) [Module.Finite A N] (n : ℕ) :
    (rPerfd_finiteCoefficientPowerHolimIso A t D p hperf N).hom ≫
      modulePowerDerivedTensorHolimProjection A (p : A) C₀ N n =
        (boundedAboveDerivedTensorModuleFunctor C₀).map (modulePowerReductionMap (p : A) N n) :=
  finiteCoefficientPowerHolimIso_projection A (p : A) C₀ N
    (rPerfd_isModuleComplete A t D p hperf) n

meta section
open Lean Elab Command
elab "assert_rperfd_power_holim_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_power_holim_projection,
    ``rPerfd_finiteCoefficientPowerHolimIso] {}
  logInfo "Actual RPerfd ordinary-quotient holim: original derived projection checked."
end

assert_rperfd_power_holim_dependencies
#print axioms rPerfd_finiteCoefficientPowerHolimIso
#print axioms rperfd_power_holim_projection

private lemma rperfd_power_holim_scalar (N : ModuleCat.{u} A) [Module.Finite A N]
    (c : RPerfd A D t p hperf) :
    let f : C₀ ⟶ C₀ := ModuleCat.ofHom (LinearMap.mulLeft A c)
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj N)))).hom ≫
        (rPerfd_finiteCoefficientPowerHolimIso A t D p hperf N).hom =
      (rPerfd_finiteCoefficientPowerHolimIso A t D p hperf N).hom ≫
        modulePowerDerivedTensorHolimMap (p : A) N f :=
  finiteCoefficientPowerHolimIso_naturality_left (p : A) N
    (ModuleCat.ofHom (LinearMap.mulLeft A c))
    (rPerfd_isModuleComplete A t D p hperf) (rPerfd_isModuleComplete A t D p hperf)

meta section
open Lean Elab Command
elab "assert_rperfd_power_holim_scalar_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_power_holim_scalar] {}
  logInfo "Actual RPerfd coefficient multiplication agrees with the original holim action."
end

assert_rperfd_power_holim_scalar_dependencies
#print axioms rperfd_power_holim_scalar

private lemma rperfd_power_holim_two_actions_zero (N : ModuleCat.{u} A)
    (c d : RPerfd A D t p hperf) (i : ℤ)
    (hc : ∀ n, HomologicalComplex.homologyMap
      (((MonoidalCategory.tensorLeft (modulePowerReduction (p : A) N n)).mapHomologicalComplex
        (.up ℤ)).map (extLift (projectiveResolution C₀)
          (ModuleCat.ofHom (LinearMap.mulLeft A c)) (projectiveResolution C₀))) i = 0)
    (hd : ∀ n, HomologicalComplex.homologyMap
      (((MonoidalCategory.tensorLeft (modulePowerReduction (p : A) N n)).mapHomologicalComplex
        (.up ℤ)).map (extLift (projectiveResolution C₀)
          (ModuleCat.ofHom (LinearMap.mulLeft A d)) (projectiveResolution C₀))) (i - 1) = 0) :
    HomologicalComplex.homologyMap (modulePowerTensorHolimMap (p : A) N
      (extLift (projectiveResolution C₀) (ModuleCat.ofHom (LinearMap.mulLeft A c))
        (projectiveResolution C₀))) i ≫
      HomologicalComplex.homologyMap (modulePowerTensorHolimMap (p : A) N
        (extLift (projectiveResolution C₀) (ModuleCat.ofHom (LinearMap.mulLeft A d))
          (projectiveResolution C₀))) i = 0 :=
  complexTowerHomotopyLimitMap_homology_comp_eq_zero A
    (modulePowerTensorTransition (p : A) N K₀) (modulePowerTensorTransition (p : A) N K₀)
    _ (modulePowerTensorTransition_naturality (p : A) N _) _ _
    (modulePowerTensorTransition_naturality (p : A) N _) i hc hd

meta section
open Lean Elab Command
elab "assert_rperfd_milnor_actions_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_power_holim_two_actions_zero] {}
  logInfo "Actual RPerfd tower: adjacent-degree zero actions give zero composite on holim homology."
end

assert_rperfd_milnor_actions_dependencies
#print axioms rperfd_power_holim_two_actions_zero

private lemma rperfd_finite_tor_product_zero (N : ModuleCat.{u} A) [Module.Finite A N]
    (g : A) (i : ℕ) (hi : 0 < i) (c d : CompletedTower A t p)
    (hc : c ∈ perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g))
    (hd : d ∈ perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g))
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) → ∀ (j : ℕ), 0 < j →
        ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
    torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) c *
        algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) d) = 0 :=
  finiteCoefficientTor_mul_zero_of_power_torsion_tests (p : A) N
    (RPerfd A D t p hperf) (rPerfd_isModuleComplete A t D p hperf) i _ _
    (fun L k hk hL => hTor L k hk hL i hi c hc)
    (fun L k hk hL => hTor L k hk hL (i + 1) (Nat.succ_pos _) d hd)

meta section
open Lean Elab Command
elab "assert_rperfd_finite_tor_product_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_finite_tor_product_zero] {}
  logInfo "Actual RPerfd: full positive torsion tests give product zero on standard finite-test Tor."
end

assert_rperfd_finite_tor_product_dependencies
#print axioms rperfd_finite_tor_product_zero

private lemma rperfd_arbitrary_tor_product_zero (N : ModuleCat.{u} A)
    (g : A) (i : ℕ) (hi : 0 < i) (c d : CompletedTower A t p)
    (hc : c ∈ perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g))
    (hd : d ∈ perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g))
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) → ∀ (j : ℕ), 0 < j →
        ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :
    torCoefficientScalarEndomorphism (RPerfd A D t p hperf) N i
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) c *
        algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) d) = 0 :=
  tor_mul_zero_of_power_torsion_tests (p : A)
    (RPerfd A D t p hperf) (rPerfd_isModuleComplete A t D p hperf) i _ _
    (fun L k hk hL => hTor L k hk hL i hi c hc)
    (fun L k hk hL => hTor L k hk hL (i + 1) (Nat.succ_pos _) d hd) N

meta section
open Lean Elab Command
elab "assert_rperfd_arbitrary_tor_product_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_arbitrary_tor_product_zero] {}
  logInfo "Actual RPerfd: product zero for every test module, with no finiteness hypothesis."
end

assert_rperfd_arbitrary_tor_product_dependencies
#print axioms rperfd_arbitrary_tor_product_zero

#print axioms rPerfd_torAlgebra_isModuleComplete
#print axioms rPerfd_torAlgebra_annihilator_iff

-- Actual completeness over the original completed-tower action, including i=0.
private lemma rperfd_tor_algebra_complete_degree_zero
    (N : ModuleCat.{u} A) [Module.Finite A N] :
    IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p)
      ((ModuleCat.restrictScalars
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
          (((ModuleCat.extendScalars (algebraMap A (RPerfd A D t p hperf))).leftDerived 0).obj N)) :=
  rPerfd_torAlgebra_isModuleComplete A t D p hperf N 0

meta section
open Lean Elab Command
elab "assert_rperfd_tor_algebra_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_tor_algebra_complete_degree_zero,
    ``rPerfd_torAlgebra_isModuleComplete, ``rPerfd_torAlgebra_annihilator_iff] {}
  logInfo "Actual algebra-valued Tor: original tower action, annihilator comparison and completeness checked."
end

assert_rperfd_tor_algebra_dependencies
#print axioms rperfd_tor_algebra_complete_degree_zero

private def rperfd_original_milnor_limit_comparison (N : ModuleCat.{u} A) (i : ℕ) :
    moduleTowerLimit A
      (fun n => (powerCokernelComplex (p : A) ((moduleTensorCochainFunctor K₀).obj N) n).homology (-(i : ℤ)))
      (fun n => (HomologicalComplex.homologyMap (powerCokernelComplexTransition (p : A)
        ((moduleTensorCochainFunctor K₀).obj N) n) (-(i : ℤ))).hom) ≃ₗ[A]
      (ModuleCat.restrictScalars (algebraMap A (RPerfd A D t p hperf))).obj
        (modulePowerTorAlgebraLimit (p : A) (RPerfd A D t p hperf) N i) :=
  modulePowerCokernelTorAlgebraLimitComparison (p : A) (RPerfd A D t p hperf) N i

private def rperfd_original_milnor_previous_comparison (N : ModuleCat.{u} A) (i : ℕ) :
    complexTowerHomologyLimOne A
      (powerCokernelComplex (p : A) ((moduleTensorCochainFunctor K₀).obj N))
      (powerCokernelComplexTransition (p : A) ((moduleTensorCochainFunctor K₀).obj N))
      (-(i : ℤ) - 1) ≃ₗ[A]
      (ModuleCat.restrictScalars (algebraMap A (RPerfd A D t p hperf))).obj
        (modulePowerTorAlgebraLimOne (p : A) (RPerfd A D t p hperf) N (i + 1)) := by
  have hi : -(i : ℤ) - 1 = -((i + 1 : ℕ) : ℤ) := by omega
  rw [hi]
  exact modulePowerCokernelTorAlgebraLimOneComparison (p : A) (RPerfd A D t p hperf) N (i + 1)

meta section
open Lean Elab Command
elab "assert_rperfd_tor_milnor_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_original_milnor_limit_comparison,
    ``rperfd_original_milnor_previous_comparison,
    ``rPerfd_torMilnor_endpoints_isModuleComplete, ``rPerfd_torMilnor_endpoints_annihilated] {}
  logInfo "Actual original Milnor endpoints: same transitions, Tor_(i+1), completeness and ideal action checked."
end

assert_rperfd_tor_milnor_dependencies
#print axioms rperfd_original_milnor_limit_comparison
#print axioms rperfd_original_milnor_previous_comparison
#print axioms rPerfd_torMilnor_endpoints_isModuleComplete
#print axioms rPerfd_torMilnor_endpoints_annihilated

private lemma rperfd_native_milnor_left (N : ModuleCat.{u} A) [Module.Finite A N] (i : ℕ) :
    (rPerfd_torMilnorShortComplex A t D p hperf N i).X₁ =
      (ModuleCat.restrictScalars
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
          (modulePowerTorAlgebraLimOne (p : A) (RPerfd A D t p hperf) N (i + 1)) := rfl

private lemma rperfd_native_milnor_middle (N : ModuleCat.{u} A) [Module.Finite A N] (i : ℕ) :
    (rPerfd_torMilnorShortComplex A t D p hperf N i).X₂ =
      (ModuleCat.restrictScalars
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
          (((ModuleCat.extendScalars (algebraMap A (RPerfd A D t p hperf))).leftDerived i).obj N) := rfl

private lemma rperfd_native_milnor_right (N : ModuleCat.{u} A) [Module.Finite A N] (i : ℕ) :
    (rPerfd_torMilnorShortComplex A t D p hperf N i).X₃ =
      (ModuleCat.restrictScalars
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))).obj
          (modulePowerTorAlgebraLimit (p : A) (RPerfd A D t p hperf) N i) := rfl

meta section
open Lean Elab Command
elab "assert_rperfd_native_milnor_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_native_milnor_left,
    ``rperfd_native_milnor_middle, ``rperfd_native_milnor_right,
    ``rPerfd_torMilnorShortComplex, ``rPerfd_torMilnorShortComplex_shortExact,
    ``rPerfd_tor_eq_zero_of_power_torsion_and_extensions] {}
  logInfo "Original completed-tower-linear Milnor sequence and full conditional Tor input checked."
end

assert_rperfd_native_milnor_dependencies
#print axioms rperfd_native_milnor_left
#print axioms rperfd_native_milnor_middle
#print axioms rperfd_native_milnor_right
#print axioms rPerfd_torMilnorShortComplex_shortExact
#print axioms rPerfd_tor_eq_zero_of_power_torsion_and_extensions

-- Apply the full conditional Cor 4.0.4, including both conclusions, using the
-- newly constructed full Tor input. The remaining inputs stay explicit.
private def rperfd_cor4_from_torsion_extensions
    [IsLocalRing D] [IsNoetherianRing D]
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hI : ∀ k : ℕ, 0 < k → IsIdempotentElem
      ((perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)).map
          (Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p) ^ k}))))
    (hExt : CompleteIdealExtensionClosed (CompletedTower A t p) (p : CompletedTower A t p)
      (perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g)))
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :=
  rPerfd_cohomology_vanishing_of_tor_idempotent A t D p hperf ht hdim hsop j₀ htp g hI
    (rPerfd_tor_eq_zero_of_power_torsion_and_extensions A t D p hperf g hExt hTor)

meta section
open Lean Elab Command
elab "assert_rperfd_cor4_torsion_extensions_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_cor4_from_torsion_extensions] {}
  logInfo "Both original conditional Cor 4.0.4 conclusions accept the full torsion/extension Tor input."
end

assert_rperfd_cor4_torsion_extensions_dependencies
#print axioms rperfd_cor4_from_torsion_extensions

#print axioms SerrePositivity.CLMST.rPerfd_tor_eq_zero_of_power_torsion_and_quotientTorOne

-- Both conclusions with the original quotient self-Tor input.
private def rperfd_cor4_from_torsion_quotientTorOne
    [IsLocalRing D] [IsNoetherianRing D]
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (j₀ : Fin h) (htp : t j₀ = (p : A)) (g : A)
    (hI : ∀ k : ℕ, 0 < k → IsIdempotentElem
      ((perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)).map
          (Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p) ^ k}))))
    (hQ : Function.Surjective (fun x : TorModule (CompletedTower A t p) 1
      ((CompletedTower A t p) ⧸ perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g))
      ((CompletedTower A t p) ⧸ perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) => (p : CompletedTower A t p) • x))
    (hTor : ∀ (L : ModuleCat.{u} A) (k : ℕ), 0 < k →
      (∀ x : L, (p : A) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ s ∈ perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g),
          torCoefficientScalarEndomorphism (RPerfd A D t p hperf) L j
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) s) = 0) :=
  rPerfd_cohomology_vanishing_of_tor_idempotent A t D p hperf ht hdim hsop j₀ htp g hI
    (rPerfd_tor_eq_zero_of_power_torsion_and_quotientTorOne A t D p hperf g hQ hTor)

meta section
open Lean Elab Command
elab "assert_rperfd_cor4_torsion_quotientTorOne_dependencies" : command => do
  let _ ← liftCoreM <| checkRPerfdDependencies [``rperfd_cor4_from_torsion_quotientTorOne] {}
  logInfo "Both Cor 4.0.4 conclusions accept the actual first quotient Tor criterion."
end
assert_rperfd_cor4_torsion_quotientTorOne_dependencies
#print axioms rperfd_cor4_from_torsion_quotientTorOne

#print axioms SerrePositivity.CLMST.rPerfd_tor_eq_zero_of_power_torsion_and_completed_quotient_mul

#print axioms SerrePositivity.CLMST.rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_power_torsion

#print axioms SerrePositivity.CLMST.rPerfd_power_torsion_tor_eq_zero_of_completedTower
#print axioms SerrePositivity.CLMST.rPerfd_cohomology_vanishing_of_completed_quotient_mul_and_tower_power_torsion

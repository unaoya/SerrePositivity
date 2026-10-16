import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFlatReductionPure
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTowerLimitBound
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFlatReductionBounded
import SerrePositivity.HomologicalAlgebra.ModelTensorFlatCriterion
import SerrePositivity.HomologicalAlgebra.ScalarExtensionTensorTests
import SerrePositivity.HomologicalAlgebra.FlatDerivedPowerReductions
import SerrePositivity.HomologicalAlgebra.ModelTensorHomologySurjective
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelTransitions
import SerrePositivity.HomologicalAlgebra.ModuleTensorCochainExact
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelTensorModel
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPowerCokernelModel
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerImageTower
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelReconstruction
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulPowerCokernelComparison
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.UniformZeroTower
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.UniformZeroTowerHomology
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTower
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionComplex
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FlatResidueLimitTorsion
import Mathlib.Util.AssertNoSorry

open SerrePositivity SerrePositivity.DerivedCompletion

assert_no_sorry smul_eq_zero_of_flat_of_mul_kernel
#print axioms smul_eq_zero_of_flat_of_mul_kernel
assert_no_sorry flat_power_torsion_bound
#print axioms flat_power_torsion_bound
assert_no_sorry smul_eq_smul_of_flat_of_mul_kernel
#print axioms smul_eq_smul_of_flat_of_mul_kernel
assert_no_sorry powerQuotient_mul_kernel_relation
#print axioms powerQuotient_mul_kernel_relation
assert_no_sorry flat_powerQuotient_torsion_relation
#print axioms flat_powerQuotient_torsion_relation
assert_no_sorry moduleTowerLimit_flat_residues_power_torsion_bound
#print axioms moduleTowerLimit_flat_residues_power_torsion_bound

-- The same bound, with no prime, regularity, or finite generation hypotheses.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (a : R) (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) :
    ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0 :=
  flat_power_torsion_bound a N h

-- A zero torsion bound is allowed when supplied by the ring itself.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (a : R) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → r = 0)
    (n : ℕ) (x : M) (hx : a ^ n • x = 0) : x = 0 := by
  simpa using flat_power_torsion_bound a 0 (by simpa using h) n x hx

-- Arbitrary universes, arbitrary transitions, and the actual standard quotient actions.
universe u v
example {R : Type u} [CommRing R] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (M : ℕ → Type v) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    [∀ j, Module (R ⧸ Ideal.span {a ^ j}) (M j)]
    [∀ j, IsScalarTower R (R ⧸ Ideal.span {a ^ j}) (M j)]
    [∀ j, Module.Flat (R ⧸ Ideal.span {a ^ j}) (M j)]
    (t : ∀ j, M (j + 1) →ₗ[R] M j) :
    ∀ m : ℕ, ∀ x : moduleTowerLimit R M t, a ^ m • x = 0 → a ^ N • x = 0 :=
  moduleTowerLimit_flat_residues_power_torsion_bound a N h M t

-- Actual error tower and uniformly zero transition composites.
assert_no_sorry moduleTowerComposite
#print axioms moduleTowerComposite
assert_no_sorry moduleTowerShift
#print axioms moduleTowerShift
assert_no_sorry moduleTowerShift_pow_apply
#print axioms moduleTowerShift_pow_apply
assert_no_sorry moduleTowerDifference_bijective_of_uniform_zero
#print axioms moduleTowerDifference_bijective_of_uniform_zero
assert_no_sorry moduleTowerLimit_subsingleton_of_uniform_zero
#print axioms moduleTowerLimit_subsingleton_of_uniform_zero
assert_no_sorry complexTowerComposite
#print axioms complexTowerComposite
assert_no_sorry complexTowerComposite_homology
#print axioms complexTowerComposite_homology
assert_no_sorry complexTowerHolim_homology_isZero_of_uniform_zero
#print axioms complexTowerHolim_homology_isZero_of_uniform_zero
assert_no_sorry complexTowerHolim_acyclic_of_uniform_zero
#print axioms complexTowerHolim_acyclic_of_uniform_zero
assert_no_sorry powerTorsionModule
#print axioms powerTorsionModule
assert_no_sorry powerTorsionTransition
#print axioms powerTorsionTransition
assert_no_sorry powerTorsionComposite_coe
#print axioms powerTorsionComposite_coe
assert_no_sorry powerTorsionComposite_eq_zero
#print axioms powerTorsionComposite_eq_zero
assert_no_sorry flat_powerTorsionTowerDifference_bijective
#print axioms flat_powerTorsionTowerDifference_bijective
assert_no_sorry powerTorsionComplex
#print axioms powerTorsionComplex
assert_no_sorry powerTorsionComplexTransition
#print axioms powerTorsionComplexTransition
assert_no_sorry powerTorsionComplexComposite_coe
#print axioms powerTorsionComplexComposite_coe
assert_no_sorry powerTorsionComplex_holim_acyclic
#print axioms powerTorsionComplex_holim_acyclic

-- No upper or lower bound on K is required for the error tower itself.
example {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : ∀ i, Module.Flat R (K.X i))
    (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) :
    (complexTowerHomotopyLimit R (powerTorsionComplex a K)
      (powerTorsionComplexTransition a K)).Acyclic :=
  powerTorsionComplex_holim_acyclic a K hK N h

-- Length zero is included when the hypothesis really makes the stages zero.
example {R : Type u} [CommRing R] (M : ℕ → Type v)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n, M (n + 1) →ₗ[R] M n)
    (h : ∀ n, moduleTowerComposite R M t n 0 = 0) :
    Function.Bijective (moduleTowerDifference R M t) :=
  moduleTowerDifference_bijective_of_uniform_zero R M t 0 h

-- Standard image, cokernel, reconstruction, and Koszul augmentation diagrams.
assert_no_sorry powerCokernelComplex
#print axioms powerCokernelComplex
assert_no_sorry powerImageComplex
#print axioms powerImageComplex
assert_no_sorry powerScalar_square
#print axioms powerScalar_square
assert_no_sorry powerCokernelComplexTransition
#print axioms powerCokernelComplexTransition
assert_no_sorry powerImageComplexTransition
#print axioms powerImageComplexTransition
assert_no_sorry powerImageComplexTransition_ι
#print axioms powerImageComplexTransition_ι
assert_no_sorry powerImageComplexTransition_factor
#print axioms powerImageComplexTransition_factor
assert_no_sorry powerTorsionComplexInclusion
#print axioms powerTorsionComplexInclusion
assert_no_sorry powerTorsionComplexInclusion_transition
#print axioms powerTorsionComplexInclusion_transition
assert_no_sorry powerTorsionComplexInclusion_factor_zero
#print axioms powerTorsionComplexInclusion_factor_zero
assert_no_sorry powerTorsionImageShortComplex
#print axioms powerTorsionImageShortComplex
assert_no_sorry powerTorsionImageShortComplex_shortExact
#print axioms powerTorsionImageShortComplex_shortExact
assert_no_sorry powerImageCokernelShortComplex
#print axioms powerImageCokernelShortComplex
assert_no_sorry powerImageCokernelShortComplex_shortExact
#print axioms powerImageCokernelShortComplex_shortExact
assert_no_sorry powerTorsionImageHolimShortComplex
#print axioms powerTorsionImageHolimShortComplex
assert_no_sorry powerTorsionImageHolimShortComplex_shortExact
#print axioms powerTorsionImageHolimShortComplex_shortExact
assert_no_sorry powerImageComplex_holim_acyclic
#print axioms powerImageComplex_holim_acyclic
assert_no_sorry powerCokernelComplexTransition_π
#print axioms powerCokernelComplexTransition_π
assert_no_sorry powerImageCokernelHolimShortComplex
#print axioms powerImageCokernelHolimShortComplex
assert_no_sorry powerImageCokernelHolimShortComplex_shortExact
#print axioms powerImageCokernelHolimShortComplex_shortExact
assert_no_sorry powerCokernelReconstruction
#print axioms powerCokernelReconstruction
assert_no_sorry powerCokernelReconstruction_eq_lift
#print axioms powerCokernelReconstruction_eq_lift
assert_no_sorry powerCokernelReconstruction_projection
#print axioms powerCokernelReconstruction_projection
assert_no_sorry powerCokernelReconstruction_quasiIso
#print axioms powerCokernelReconstruction_quasiIso
assert_no_sorry powerScalarCokernelShortComplex
#print axioms powerScalarCokernelShortComplex
assert_no_sorry koszulPowerCokernelAugmentation
#print axioms koszulPowerCokernelAugmentation
assert_no_sorry koszulPowerCokernelAugmentation_inr
#print axioms koszulPowerCokernelAugmentation_inr
assert_no_sorry koszulPowerCokernelAugmentation_transition
#print axioms koszulPowerCokernelAugmentation_transition
assert_no_sorry koszulPowerCokernelComparison
#print axioms koszulPowerCokernelComparison
assert_no_sorry complexCompletionUnit_comp_koszulPowerCokernelComparison
#print axioms complexCompletionUnit_comp_koszulPowerCokernelComparison
assert_no_sorry koszulPowerCokernelComparison_quasiIso
#print axioms koszulPowerCokernelComparison_quasiIso

open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard

-- The actual augmentation, with no regularity or boundedness added to K.
example {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : ∀ i, Module.Flat R (K.X i))
    (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (koszulPowerCokernelComparison a K) :=
  koszulPowerCokernelComparison_quasiIso a K hK N h hc

-- The unit diagram holds without even the torsion bound or completeness.
example {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    complexCompletionUnit R a K ≫ koszulPowerCokernelComparison a K =
      powerCokernelReconstruction a K :=
  complexCompletionUnit_comp_koszulPowerCokernelComparison a K

-- Actual quotient tensor and derived reduction models.
assert_no_sorry SerrePositivity.moduleTensorCochainFunctor_linear
#print axioms SerrePositivity.moduleTensorCochainFunctor_linear
assert_no_sorry SerrePositivity.moduleTensorCochain_exact
#print axioms SerrePositivity.moduleTensorCochain_exact
assert_no_sorry SerrePositivity.moduleTensorCochain_map_epi
#print axioms SerrePositivity.moduleTensorCochain_map_epi
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientCoefficientMap
#print axioms SerrePositivity.DerivedCompletion.powerQuotientCoefficientMap
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientCoefficientMap_epi
#print axioms SerrePositivity.DerivedCompletion.powerQuotientCoefficientMap_epi
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientCoefficientShortComplex
#print axioms SerrePositivity.DerivedCompletion.powerQuotientCoefficientShortComplex
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientCoefficientShortComplex_exact
#print axioms SerrePositivity.DerivedCompletion.powerQuotientCoefficientShortComplex_exact
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientTensorMap
#print axioms SerrePositivity.DerivedCompletion.powerQuotientTensorMap
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientTensorMap_zero
#print axioms SerrePositivity.DerivedCompletion.powerQuotientTensorMap_zero
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientTensorShortComplex
#print axioms SerrePositivity.DerivedCompletion.powerQuotientTensorShortComplex
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientTensorShortComplex_exact
#print axioms SerrePositivity.DerivedCompletion.powerQuotientTensorShortComplex_exact
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientTensorMap_epi
#print axioms SerrePositivity.DerivedCompletion.powerQuotientTensorMap_epi
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelTensorModelIso
#print axioms SerrePositivity.DerivedCompletion.powerCokernelTensorModelIso
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelTensorModelIso_π
#print axioms SerrePositivity.DerivedCompletion.powerCokernelTensorModelIso_π
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientCoefficientIso
#print axioms SerrePositivity.DerivedCompletion.powerQuotientCoefficientIso
assert_no_sorry SerrePositivity.DerivedCompletion.derivedPowerCokernelModelIso
#print axioms SerrePositivity.DerivedCompletion.derivedPowerCokernelModelIso
assert_no_sorry SerrePositivity.DerivedCompletion.derivedPowerCokernelHomologyIso
#print axioms SerrePositivity.DerivedCompletion.derivedPowerCokernelHomologyIso
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernel_homology_isZero_of_reduction
#print axioms SerrePositivity.DerivedCompletion.powerCokernel_homology_isZero_of_reduction

noncomputable section

-- Zero power, arbitrary upper bound, and no regularity assumption on a.
example {R : Type u} [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {a ^ 0}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ 0}))).obj X)).obj ≅
        DerivedCategory.Q.obj
          (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex 0) :=
  derivedPowerCokernelModelIso a 0 X

-- Actual quotient homology, with its restricted scalar action, in every degree.
example {R : Type u} [CommRing R] (a : R) (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ) :
    (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology i ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ n})) i).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj) :=
  derivedPowerCokernelHomologyIso a n X i

end

-- Pure flat power reductions and the actual surjective H0 transitions.
assert_no_sorry SerrePositivity.derived_pure_flat_of_modelTensor_tests
#print axioms SerrePositivity.derived_pure_flat_of_modelTensor_tests
assert_no_sorry SerrePositivity.derivedBaseChange_pure_flat_of_tensor_tests
#print axioms SerrePositivity.derivedBaseChange_pure_flat_of_tensor_tests
assert_no_sorry SerrePositivity.modelTensor_isZero_of_power_annihilated
#print axioms SerrePositivity.modelTensor_isZero_of_power_annihilated
assert_no_sorry SerrePositivity.derived_power_reduction_pure_flat
#print axioms SerrePositivity.derived_power_reduction_pure_flat
assert_no_sorry SerrePositivity.modelTensor_homology_zero_map_surjective_of_power_annihilated
#print axioms SerrePositivity.modelTensor_homology_zero_map_surjective_of_power_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.powerPrincipalIdeal_antitone_step
#print axioms SerrePositivity.DerivedCompletion.powerPrincipalIdeal_antitone_step
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientCoefficientTransition
#print axioms SerrePositivity.DerivedCompletion.powerQuotientCoefficientTransition
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientCoefficientMap_transition
#print axioms SerrePositivity.DerivedCompletion.powerQuotientCoefficientMap_transition
assert_no_sorry SerrePositivity.DerivedCompletion.powerQuotientCoefficientTransition_epi
#print axioms SerrePositivity.DerivedCompletion.powerQuotientCoefficientTransition_epi
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelTensorModelIso_transition
#print axioms SerrePositivity.DerivedCompletion.powerCokernelTensorModelIso_transition
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernel_homology_zero_transition_surjective
#print axioms SerrePositivity.DerivedCompletion.powerCokernel_homology_zero_transition_surjective

section PowerInput
open CategoryTheory.Limits
variable {R : Type u} [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))

-- All powers, with no ring torsion bound or completeness required for this step.
example (n : ℕ) :
    ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj.IsGE 0 ∧
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj.IsLE 0 ∧
      Module.Flat (R ⧸ Ideal.span {a ^ n})
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ n})) 0).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj) :=
  derived_power_reduction_pure_flat a X hPure hFlat n

-- The actual zero-power transition is included.
example : Function.Surjective (homologyMap
    (powerCokernelComplexTransition a (boundedAboveDerivedChosenModel X).complex 0) 0) :=
  powerCokernel_homology_zero_transition_surjective a X hPure hFlat 0

end PowerInput

-- Full G9: purity of X itself and bounded torsion of its actual H0.
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernel_homology_isZero_of_flat_reduction
#print axioms SerrePositivity.DerivedCompletion.powerCokernel_homology_isZero_of_flat_reduction
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelHomologyDifference_surjective
#print axioms SerrePositivity.DerivedCompletion.powerCokernelHomologyDifference_surjective
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernel_holim_homology_isZero
#print axioms SerrePositivity.DerivedCompletion.powerCokernel_holim_homology_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.completeFlatReductionH0LimitIso
#print axioms SerrePositivity.DerivedCompletion.completeFlatReductionH0LimitIso
assert_no_sorry SerrePositivity.DerivedCompletion.derived_pure_of_complete_flat_reduction
#print axioms SerrePositivity.DerivedCompletion.derived_pure_of_complete_flat_reduction
assert_no_sorry SerrePositivity.DerivedCompletion.moduleTowerLimit_power_torsion_bound_of_relations
#print axioms SerrePositivity.DerivedCompletion.moduleTowerLimit_power_torsion_bound_of_relations
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelH0_power_annihilated
#print axioms SerrePositivity.DerivedCompletion.powerCokernelH0_power_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelH0_torsion_relation
#print axioms SerrePositivity.DerivedCompletion.powerCokernelH0_torsion_relation
assert_no_sorry SerrePositivity.DerivedCompletion.derived_pure_bounded_torsion_of_complete_flat_reduction
#print axioms SerrePositivity.DerivedCompletion.derived_pure_bounded_torsion_of_complete_flat_reduction

-- Exact original G9 signature, with its actual derived quotient and completion.
example {T : Type u} [CommRing T] (p : ℕ) [Fact p.Prime]
    (X : DerivedCategory.Minus (ModuleCat.{u} T))
    (hT : ∃ N : ℕ, ∀ n : ℕ, ∀ t : T, (p : T) ^ n * t = 0 → (p : T) ^ N * t = 0)
    (hX : IsComplete T (p : T) X.obj)
    (hPure : ∀ i : ℤ, i ≠ 0 → CategoryTheory.Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (T ⧸ Ideal.span {(p : T)})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : T)}))).obj X).obj))
    (hFlat : Module.Flat (T ⧸ Ideal.span {(p : T)})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (T ⧸ Ideal.span {(p : T)})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : T)}))).obj X).obj)) :
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ n : ℕ,
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) 0).obj X.obj,
          (p : T) ^ n • x = 0 → (p : T) ^ N • x = 0 :=
  derived_pure_bounded_torsion_of_complete_flat_reduction (p : T) X hPure hFlat hT hX

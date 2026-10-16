import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorH0Comparison
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RegularTensorReduction
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorModuleReduction
import SerrePositivity.BhattScholze.DeltaRootSourceNonpositive
import SerrePositivity.BhattScholze.PerfectOrientedPrism
import Mathlib.Util.AssertNoSorry

/-! Concrete input checks only: common modules never import this BS-facing audit. -/
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

section RootSource
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "r₀" => deltaRootRelationFamily (p := p) b

private lemma root_source_completed_augmentation_h0 :
    letI := deltaDivisionSourceEvaluationAlgebra E₀ r₀
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} L₀) 0).map
      (boundedAboveCompletedTensorAlgebraAugmentation L₀ (p : L₀) P₀ L₀).hom.hom.hom) := by
  let := deltaDivisionSourceEvaluationAlgebra E₀ r₀
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
  exact completedTensorAlgebraAugmentation_h0_isIso L₀ (p : L₀) P₀ L₀

private def root_source_completed_F3 :
    letI := deltaDivisionSourceEvaluationAlgebra E₀ r₀
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
    letI : Module L₀ L₀ := Algebra.toModule
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra L₀ (p : L₀) P₀ L₀)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra L₀ (p : L₀) P₀ L₀)
    letI := pdCompletionCommRing (P₀ ⊗[L₀] L₀) p 0
    letI := pdCompletionBaseAlgebra L₀ (P₀ ⊗[L₀] L₀) p 0
    (DerivedCategory.homologyFunctor (ModuleCat.{u} L₀) 0).obj
      (boundedAboveCompletedTensorAlgebra L₀ (p : L₀) P₀ L₀).X.obj ≃ₐ[L₀]
        PDCompletionH0 (P₀ ⊗[L₀] L₀) p 0 := by
  letI := deltaDivisionSourceEvaluationAlgebra E₀ r₀
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
  letI : Module L₀ L₀ := Algebra.toModule
  exact completedTensorH0PDAlgEquiv L₀ p P₀ L₀

-- Verify the actual coefficient-restricted augmentation through both original completion maps.
private lemma root_source_iterated_comparison_h0 :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (deltaRootSourceRawIteratedComparison D d b).hom) := by
  apply boundedAboveDerivedCompletion_h0_map_isIso A d
  · exact boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (deltaRootSourceCoefficient_isLE_zero D d b)
  · exact boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (deltaRootSourceRawCoefficient_isLE_zero D d b)
  · exact boundedAboveDerivedCompletion_h0_map_isIso A (p : A) _
      (deltaRootSourceCoefficient_isLE_zero D d b)
      (deltaRootSourceRawCoefficient_isLE_zero D d b)
      (deltaRootSourceRawCoefficientAugmentation_h0_isIso D d b)
end RootSource

-- Supply both ordinary-residue Tor inputs using the prism, rather than the original perfectoid ring.
private lemma perfect_prism_root_residue_tor_inputs
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (d : A) (b : σ → A) (n : ℕ) :
    let P₀ := MvPolynomial σ A
    let L₀ := RelativeFreeDeltaRing (R := P₀) σ
    let E₀ := polynomialRankOneDeltaStructure σ P.deltaStructure
    let β := deltaDivisionSourceEval E₀ (deltaRootRelationFamily (p := p) b)
    let α := deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
    let q := Ideal.Quotient.mk (Ideal.span {(p : L₀) ^ n})
    scalarExtensionTorVanishing q (baseChangeScalarModule β) ∧
      scalarExtensionTorVanishing q (baseChangeScalarModule α) := by
  let P₀ := MvPolynomial σ A
  let L₀ := RelativeFreeDeltaRing (R := P₀) σ
  let E₀ := polynomialRankOneDeltaStructure σ P.deltaStructure
  have hpP : IsSMulRegular P₀ (p : P₀) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hP.p_mul_injective).of_flat (S := P₀)
  have hpL : IsSMulRegular L₀ (p : L₀) := by
    simpa only [map_natCast] using hpP.of_flat (S := L₀)
  constructor
  · apply scalarExtensionTorVanishing_principal_pow_of_regular (p : L₀) hpL
    change Function.Injective (fun x : P₀ ↦
      deltaDivisionSourceEval E₀ (deltaRootRelationFamily (p := p) b) (p : L₀) * x)
    simpa only [map_natCast] using
      (show Function.Injective (fun x : P₀ ↦ (p : P₀) * x) from hpP)
  · apply scalarExtensionTorVanishing_principal_pow_of_regular (p : L₀) hpL
    change Function.Injective (fun x : L₀ ↦
      deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d) (p : L₀) * x)
    simpa only [map_natCast] using
      (show Function.Injective (fun x : L₀ ↦ (p : L₀) * x) from hpL)

section PrismaticReduction
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (d : A) (b : σ → A) (n : ℕ)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ P.deltaStructure
local notation "β" => deltaDivisionSourceEval E₀ (deltaRootRelationFamily (p := p) b)
local notation "α" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "I₀" => Ideal.span {(p : L₀) ^ n}
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "X₀" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)

private def root_prism_completed_reduction :
    (boundedAboveDerivedBaseChange q₀).obj
      ((boundedAboveDerivedCompletionFunctor L₀ (p : L₀)).obj X₀) ≅
        boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj ((quotientModuleFunctor I₀).obj Mβ),
            boundedAboveDerivedSingleFunctor.obj ((quotientModuleFunctor I₀).obj Mα)) := by
  have hpP : IsSMulRegular P₀ (p : P₀) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hP.p_mul_injective).of_flat (S := P₀)
  have hpL : IsSMulRegular L₀ (p : L₀) := by
    simpa only [map_natCast] using hpP.of_flat (S := L₀)
  obtain ⟨hβ, hα⟩ := perfect_prism_root_residue_tor_inputs P hP d b n
  exact boundedAboveDerivedCompletedTensorQuotientModuleIso L₀ (p : L₀) hpL n Mβ Mα hβ hα

-- The actual image of the original completion unit is standard quotient base change.
private lemma root_prism_completed_reduction_unit :
    (boundedAboveDerivedBaseChange q₀).map
        ((boundedAboveDerivedCompletionUnit L₀ (p : L₀)).app X₀) ≫
      (root_prism_completed_reduction P hP d b n).hom =
        (derivedTensorQuotientModuleIso I₀ Mβ Mα
          (perfect_prism_root_residue_tor_inputs P hP d b n).1
          (perfect_prism_root_residue_tor_inputs P hP d b n).2).hom := by
  apply boundedAboveDerivedCompletedTensorQuotientModuleIso_unit
end PrismaticReduction

assert_no_sorry root_source_completed_augmentation_h0
#print axioms root_source_completed_augmentation_h0
assert_no_sorry root_source_completed_F3
#print axioms root_source_completed_F3
assert_no_sorry root_source_iterated_comparison_h0
#print axioms root_source_iterated_comparison_h0
assert_no_sorry perfect_prism_root_residue_tor_inputs
#print axioms perfect_prism_root_residue_tor_inputs
assert_no_sorry root_prism_completed_reduction
#print axioms root_prism_completed_reduction
assert_no_sorry root_prism_completed_reduction_unit
#print axioms root_prism_completed_reduction_unit

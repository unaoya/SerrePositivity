import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrism
import SerrePositivity.BhattScholze.Andre.Perfection.DeltaAlgebra
import SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootPerfectoid
import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDelta
import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteResidue
import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
import SerrePositivity.BhattScholze.Andre.Envelope.RootFamilySource
import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source
import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
import SerrePositivity.BhattScholze.Delta.DividedPower.Principal.PrincipalDP
import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection
import SerrePositivity.BhattScholze.Delta.Division.Family
import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing
import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
import SerrePositivity.BhattScholze.Delta.Division.Source
import SerrePositivity.BhattScholze.Andre.Envelope.Normalized
import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeWitt
import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
import SerrePositivity.CommutativeAlgebra.DividedPowers.RankOneDP
import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
import SerrePositivity.BhattScholze.Delta.Division.Relations
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Util.AssertNoSorry

/-! Focused dependency checks for the BS refactoring steps.

Build the imported project modules before running `lake env lean` on this file.
The existing BS foundation and B4 audits remain the integration checks.
-/

-- R1d: preserve the actual scalar actions and quotient comparisons.
assert_no_sorry SerrePositivity.BhattScholze.pdCompletionH0_self_complete_p
assert_no_sorry SerrePositivity.BhattScholze.pdCompletionH0_self_complete_d
assert_no_sorry SerrePositivity.BhattScholze.existsUnique_pdCompletionRingHom
assert_no_sorry SerrePositivity.BhattScholze.pdCompletionRingHom_ext
assert_no_sorry SerrePositivity.BhattScholze.OrientedPrism.Hom.quotientMap_surjective
assert_no_sorry SerrePositivity.BhattScholze.exists_perfectDeltaPDQuotientEquiv
assert_no_sorry SerrePositivity.BhattScholze.exists_perfectDeltaPDQuotientEquiv_of_perfectoidExtension

#print axioms SerrePositivity.BhattScholze.pdCompletionH0_self_complete_p
#print axioms SerrePositivity.BhattScholze.pdCompletionH0_self_complete_d
#print axioms SerrePositivity.BhattScholze.OrientedPrism.Hom.quotientMap_surjective
#print axioms SerrePositivity.BhattScholze.exists_perfectDeltaPDQuotientEquiv
#print axioms SerrePositivity.BhattScholze.exists_perfectDeltaPDQuotientEquiv_of_perfectoidExtension

-- R2a: moving declarations keeps their public names and inverse-map contracts.
assert_no_sorry SerrePositivity.BhattScholze.wittTwoMap
assert_no_sorry SerrePositivity.BhattScholze.wittTwoMap_coeff
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.IsDeltaHom.symm
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv_symm_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv_symm_isDeltaHom

#print axioms SerrePositivity.BhattScholze.wittTwoMap
#print axioms SerrePositivity.BhattScholze.DeltaStructure.IsDeltaHom.symm

-- R1a: the original normalized module and its scalar action stay fixed.
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionNormalizedModuleDirectLimit_moduleFlat
#print axioms SerrePositivity.BhattScholze.deltaDivisionNormalizedModuleDirectLimit_moduleFlat

-- R1b: retain the concrete evaluation diagrams and residue coefficient rings.
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionEvaluationSource_tor_subsingleton_of_preservesColimit
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionEvaluationSourceFamily_tor_subsingleton
assert_no_sorry SerrePositivity.BhattScholze.deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
#print axioms SerrePositivity.BhattScholze.deltaDivisionEvaluationSource_tor_subsingleton_of_preservesColimit
#print axioms SerrePositivity.BhattScholze.deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit

-- R1c: the support and regularity statements keep their original generality.
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeWittInverseVariable_mem_supported
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeWittInverseMap_mem_supported
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeWittSupportedEquiv
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFirstRelation_isSMulRegular
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteStage_next_isSMulRegular_of_frobenius_regular
#print axioms SerrePositivity.BhattScholze.relativeFreeWittSupportedEquiv
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteStage_next_isSMulRegular_of_frobenius_regular

-- R3a: general DP maps and bases under the original specialized public signatures.
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPBaseChangeMap
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPBaseChangeMap_tmul
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPBaseChangeMap_dp
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPPrimeBasis
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPPrimeBasis_apply
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPPrime_moduleFree
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPPrime_p_mul_injective
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPBaseChangeMap_bijective
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPBaseChangeEquiv
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPBaseChangeEquiv_tmul
#print axioms SerrePositivity.BhattScholze.rankOneDPPrimeBasis
#print axioms SerrePositivity.BhattScholze.rankOneDPBaseChangeEquiv

-- Keep the explicit prime instance and the former binder order, including unused hypotheses.
noncomputable example : ∀ {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A],
    (∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) →
    Function.Injective (fun a : A ↦ (p : A) * a) →
    Module.Basis ℕ A (DividedPowerAlgebra A A) :=
  @SerrePositivity.BhattScholze.rankOneDPPrimeBasis

-- R2b: transport along the existing equivalences, including the raw H0 scalar actions.
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.comapEquiv
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.comapEquiv_delta
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.comapEquiv_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.comapEquiv_symm_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionSourceTensorDelta
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv_isDeltaHom
#print axioms SerrePositivity.BhattScholze.DeltaStructure.comapEquiv
#print axioms SerrePositivity.BhattScholze.DeltaStructure.comapEquiv_delta
#print axioms SerrePositivity.BhattScholze.DeltaStructure.comapEquiv_isDeltaHom
#print axioms SerrePositivity.BhattScholze.DeltaStructure.comapEquiv_symm_isDeltaHom
#print axioms SerrePositivity.BhattScholze.deltaDivisionSourceTensorDelta

-- R2e: the generator formula lives in the general delta-ideal layer under its old name.
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.deltaClosure_span_eq_span_generator_iterates
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.deltaClosure_eq_span_iterates
#print axioms SerrePositivity.BhattScholze.DeltaStructure.deltaClosure_span_eq_span_generator_iterates
#print axioms SerrePositivity.BhattScholze.DeltaStructure.deltaClosure_eq_span_iterates

-- R3b: general relation transport and the old specialized base-change equivalence.
assert_no_sorry SerrePositivity.BhattScholze.rankOneDPBaseChangeMap_relation
assert_no_sorry SerrePositivity.BhattScholze.principalDPBaseChangeUniversal_relationIdeal
assert_no_sorry SerrePositivity.BhattScholze.principalDPBaseChangeUniversalEquiv
assert_no_sorry SerrePositivity.BhattScholze.principalDPBaseChange_relationIdeal
assert_no_sorry SerrePositivity.BhattScholze.principalDPBaseChangeEquiv
assert_no_sorry SerrePositivity.BhattScholze.principalDPBaseChangeEquiv_coeff
assert_no_sorry SerrePositivity.BhattScholze.principalDPBaseChangeEquiv_tmul_generator
#print axioms SerrePositivity.BhattScholze.rankOneDPBaseChangeMap_relation
#print axioms SerrePositivity.BhattScholze.principalDPBaseChangeEquiv
#print axioms SerrePositivity.BhattScholze.principalDPBaseChangeEquiv_tmul_generator

-- R4a: compare the original first-coefficient maps with the generic monic quotient.
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal_eq_base_sup
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFirstPowerEvaluation_eq_baseQuotient
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialToPowerCover_surjective
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFirstPowerEvaluation_kills
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialToPowerCover_comp_backward
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFirstCoefficientPowerEquiv
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFirstResiduePowerPolynomialEquiv
#print axioms SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal_eq_base_sup
#print axioms SerrePositivity.BhattScholze.deltaDivisionFirstPowerEvaluation_eq_baseQuotient
#print axioms SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialToPowerCover_surjective
#print axioms SerrePositivity.BhattScholze.deltaDivisionFirstCoefficientPowerEquiv

-- R2c: generic polynomial sections, their calculation API, and the original universal maps.
assert_no_sorry SerrePositivity.BhattScholze.polynomialDeltaSection
assert_no_sorry SerrePositivity.BhattScholze.polynomialDeltaSection_C
assert_no_sorry SerrePositivity.BhattScholze.polynomialDeltaSection_X
assert_no_sorry SerrePositivity.BhattScholze.polynomialDeltaSection_projection
assert_no_sorry SerrePositivity.BhattScholze.polynomialDeltaStructure
assert_no_sorry SerrePositivity.BhattScholze.polynomialDeltaStructure_delta_C
assert_no_sorry SerrePositivity.BhattScholze.polynomialDeltaStructure_delta_X
assert_no_sorry SerrePositivity.BhattScholze.polynomialDeltaStructure_C_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.isDeltaHom_mvPolynomial_of_sectionHom_comp_C
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.isDeltaHom_mvPolynomial
assert_no_sorry SerrePositivity.BhattScholze.freeDeltaEval_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeDeltaEval_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStepSection_naturality
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_delta_image
#print axioms SerrePositivity.BhattScholze.polynomialDeltaSection_C
#print axioms SerrePositivity.BhattScholze.polynomialDeltaSection_X
#print axioms SerrePositivity.BhattScholze.polynomialDeltaStructure
#print axioms SerrePositivity.BhattScholze.DeltaStructure.isDeltaHom_mvPolynomial
#print axioms SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStepSection_naturality

section PolynomialSectionContracts
open SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (σ : Type*)

-- Preserve the former W₂ eval₂Hom functions, not only isomorphic delta rings.
noncomputable example (D : DeltaStructure p R) : relativeFreeDeltaSection σ D =
    MvPolynomial.eval₂Hom ((wittTwoMap MvPolynomial.C).comp D.sectionHom)
      (fun v ↦ TruncatedWittVector.mk p (fun i ↦
        if i = 0 then MvPolynomial.X v else MvPolynomial.X (v.1, v.2 + 1))) := rfl

noncomputable example (D : DeltaStructure p R) : polynomialRankOneDeltaSection σ D =
    MvPolynomial.eval₂Hom ((wittTwoMap MvPolynomial.C).comp D.sectionHom)
      (fun s ↦ TruncatedWittVector.mk p (fun i ↦
        if i = 0 then MvPolynomial.X s else 0)) := rfl
end PolynomialSectionContracts

-- R2d: the original transition functions and direct limits are unchanged.
assert_no_sorry SerrePositivity.BhattScholze.deltaDirectLimitSection
#print axioms SerrePositivity.BhattScholze.deltaDirectLimitSection
assert_no_sorry SerrePositivity.BhattScholze.deltaDirectLimitSection_of
#print axioms SerrePositivity.BhattScholze.deltaDirectLimitSection_of
assert_no_sorry SerrePositivity.BhattScholze.deltaDirectLimitSection_projection
#print axioms SerrePositivity.BhattScholze.deltaDirectLimitSection_projection
assert_no_sorry SerrePositivity.BhattScholze.deltaDirectLimitStructure
#print axioms SerrePositivity.BhattScholze.deltaDirectLimitStructure
assert_no_sorry SerrePositivity.BhattScholze.deltaDirectLimitStructure_delta_of
#print axioms SerrePositivity.BhattScholze.deltaDirectLimitStructure_delta_of
assert_no_sorry SerrePositivity.BhattScholze.deltaDirectLimitOf_isDeltaHom
#print axioms SerrePositivity.BhattScholze.deltaDirectLimitOf_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.deltaDirectLimitLift_isDeltaHom
#print axioms SerrePositivity.BhattScholze.deltaDirectLimitLift_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.deltaPerfection_isPerfect
#print axioms SerrePositivity.BhattScholze.deltaPerfection_isPerfect
assert_no_sorry SerrePositivity.BhattScholze.existsUnique_deltaPerfectionHom
#print axioms SerrePositivity.BhattScholze.existsUnique_deltaPerfectionHom
assert_no_sorry SerrePositivity.BhattScholze.deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom
#print axioms SerrePositivity.BhattScholze.deltaAdjoinDivisionFiniteColimitToFull_isDeltaHom

-- R3c: retain p-regularity and mod-p regularity; p-locality is unnecessary.
assert_no_sorry SerrePositivity.BhattScholze.principalDPRelation_mod_p_isSMulRegular_of_p_mul_injective
#print axioms SerrePositivity.BhattScholze.principalDPRelation_mod_p_isSMulRegular_of_p_mul_injective
assert_no_sorry SerrePositivity.BhattScholze.principalDPPresentation_p_mul_injective_of_regular_mod
#print axioms SerrePositivity.BhattScholze.principalDPPresentation_p_mul_injective_of_regular_mod
assert_no_sorry SerrePositivity.BhattScholze.principalDPRelation_mod_p_isSMulRegular
#print axioms SerrePositivity.BhattScholze.principalDPRelation_mod_p_isSMulRegular
assert_no_sorry SerrePositivity.BhattScholze.principalDPPresentation_p_mul_injective
#print axioms SerrePositivity.BhattScholze.principalDPPresentation_p_mul_injective

-- R4b: arbitrary nonzero exponents, including the graph relations of exponent one.
assert_no_sorry SerrePositivity.BhattScholze.monicPowerFamilyRelation_isSMulRegular
#print axioms SerrePositivity.BhattScholze.monicPowerFamilyRelation_isSMulRegular
assert_no_sorry SerrePositivity.BhattScholze.deltaRootSubsetQuotient_remaining_isSMulRegular_of_ne_zero
#print axioms SerrePositivity.BhattScholze.deltaRootSubsetQuotient_remaining_isSMulRegular_of_ne_zero
assert_no_sorry SerrePositivity.BhattScholze.deltaRootRelation_list_isWeaklyRegular_of_ne_zero
#print axioms SerrePositivity.BhattScholze.deltaRootRelation_list_isWeaklyRegular_of_ne_zero
assert_no_sorry SerrePositivity.BhattScholze.deltaRootRelation_fin_isWeaklyRegular_of_ne_zero
#print axioms SerrePositivity.BhattScholze.deltaRootRelation_fin_isWeaklyRegular_of_ne_zero
assert_no_sorry SerrePositivity.BhattScholze.deltaRootRelation_fin_isKoszulResolution_of_ne_zero
#print axioms SerrePositivity.BhattScholze.deltaRootRelation_fin_isKoszulResolution_of_ne_zero
assert_no_sorry SerrePositivity.BhattScholze.deltaRootRelation_map_fin_isKoszulResolution_of_ne_zero
#print axioms SerrePositivity.BhattScholze.deltaRootRelation_map_fin_isKoszulResolution_of_ne_zero
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionSourceGraph_fin_isWeaklyRegular
#print axioms SerrePositivity.BhattScholze.deltaDivisionSourceGraph_fin_isWeaklyRegular

-- R4c: validated refactoring contracts.
-- R4c: reuse existing p-regularity transport and Witt ghost injectivity.
assert_no_sorry SerrePositivity.BhattScholze.deltaRootSource_ghostMap_injective
#print axioms SerrePositivity.BhattScholze.deltaRootSource_ghostMap_injective

assert_no_sorry SerrePositivity.BhattScholze.deltaRootFamilyRaw_p_mul_injective_of_p_regular
#print axioms SerrePositivity.BhattScholze.deltaRootFamilyRaw_p_mul_injective_of_p_regular

assert_no_sorry SerrePositivity.BhattScholze.deltaRootFamilyCompletedModP_homology_isZero_of_p_regular
#print axioms SerrePositivity.BhattScholze.deltaRootFamilyCompletedModP_homology_isZero_of_p_regular

assert_no_sorry SerrePositivity.BhattScholze.deltaRootFamilyCompletedModPH0_faithfullyFlat_of_p_regular
#print axioms SerrePositivity.BhattScholze.deltaRootFamilyCompletedModPH0_faithfullyFlat_of_p_regular

assert_no_sorry SerrePositivity.BhattScholze.deltaRootFamilySourceQuotientDerivedH0_faithfullyFlat
#print axioms SerrePositivity.BhattScholze.deltaRootFamilySourceQuotientDerivedH0_faithfullyFlat

assert_no_sorry SerrePositivity.BhattScholze.deltaRootBoundedSupportQuotientDerivedH0_faithfullyFlat
#print axioms SerrePositivity.BhattScholze.deltaRootBoundedSupportQuotientDerivedH0_faithfullyFlat

-- R5a: validated refactoring contracts.
section R5AContracts

/- Focused R5a audit: new extensionality APIs, existing universal/comparison consumers,
   and definitional preservation of the two chosen comparison maps. -/
open SerrePositivity.BhattScholze SerrePositivity.DerivedCompletion
universe u
section ChosenMaps
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
variable (E : DeltaStructure p B) (b : B)
example :
    letI := pdCompletionCommRing (DeltaPerfection E) p (deltaPerfectionOf E 0 b)
    letI := pdCompletionCommRing (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b)
    (deltaPerfectionPDCompletionEquiv E b).toRingHom =
      deltaPerfectionPDCompletionComparison E b := rfl
example :
    letI := pdCompletionCommRing (DeltaPerfection E) p (deltaPerfectionOf E 0 b)
    letI := pdCompletionCommRing (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b)
    (deltaPerfectionPDCompletionEquiv E b).symm.toRingHom =
      deltaPerfectionPDCompletionInverse E b := rfl
end ChosenMaps

assert_no_sorry SerrePositivity.BhattScholze.deltaPerfectionHom_ext
assert_no_sorry SerrePositivity.BhattScholze.deltaPerfectionPDCompletionHom_ext
assert_no_sorry SerrePositivity.BhattScholze.pCompletedDeltaPerfectionPDCompletionHom_ext
assert_no_sorry SerrePositivity.BhattScholze.existsUnique_deltaPerfectionPDCompletionHom
assert_no_sorry SerrePositivity.BhattScholze.existsUnique_pCompletedDeltaPerfectionPDCompletionHom
assert_no_sorry SerrePositivity.BhattScholze.deltaPerfectionPDCompletionComparison
assert_no_sorry SerrePositivity.BhattScholze.deltaPerfectionPDCompletionComparison_spec
assert_no_sorry SerrePositivity.BhattScholze.deltaPerfectionPDCompletionInverse
assert_no_sorry SerrePositivity.BhattScholze.deltaPerfectionPDCompletionInverse_spec
assert_no_sorry SerrePositivity.BhattScholze.deltaPerfectionPDCompletionEquiv
assert_no_sorry SerrePositivity.BhattScholze.deltaPerfectionPDCompletionEquiv_spec

#print axioms SerrePositivity.BhattScholze.deltaPerfectionHom_ext
#print axioms SerrePositivity.BhattScholze.deltaPerfectionPDCompletionHom_ext
#print axioms SerrePositivity.BhattScholze.pCompletedDeltaPerfectionPDCompletionHom_ext
#print axioms SerrePositivity.BhattScholze.existsUnique_deltaPerfectionPDCompletionHom
#print axioms SerrePositivity.BhattScholze.existsUnique_pCompletedDeltaPerfectionPDCompletionHom
#print axioms SerrePositivity.BhattScholze.deltaPerfectionPDCompletionComparison
#print axioms SerrePositivity.BhattScholze.deltaPerfectionPDCompletionComparison_spec
#print axioms SerrePositivity.BhattScholze.deltaPerfectionPDCompletionInverse
#print axioms SerrePositivity.BhattScholze.deltaPerfectionPDCompletionInverse_spec
#print axioms SerrePositivity.BhattScholze.deltaPerfectionPDCompletionEquiv
#print axioms SerrePositivity.BhattScholze.deltaPerfectionPDCompletionEquiv_spec
end R5AContracts

-- R5b: validated refactoring contracts.
section R5BContracts

/- Focused R5b audit: all presentation declarations, both consumers,
   and preservation of the selected recovery equivalence, generator and quotient maps. -/
open SerrePositivity SerrePositivity.BhattScholze
universe u
section OriginalChoices
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
variable [IsAdicComplete (Ideal.span {(p : A)}) A]
example : perfectPrismWittRecoveryEquiv P hP =
    perfectDeltaWittRecoveryEquiv P.deltaStructure hP := rfl
example : perfectPrismWittGenerator P hP =
    (perfectDeltaWittRecoveryEquiv P.deltaStructure hP).symm P.generator := rfl
example (hI : P.ideal =
    (Ideal.span {(perfectDeltaWittRecoveryEquiv P.deltaStructure hP).symm P.generator}).map
      (perfectDeltaWittRecoveryEquiv P.deltaStructure hP).toRingHom) :
    perfectPrismWittQuotientEquiv P hP =
      Ideal.quotientEquiv _ _ (perfectDeltaWittRecoveryEquiv P.deltaStructure hP) hI := rfl
example (x : WittVector p (ModP A p)) :
    perfectPrismWittQuotientEquiv P hP (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk P.ideal (perfectPrismWittRecoveryEquiv P hP x) := rfl
example (a : A) :
    (perfectPrismWittQuotientEquiv P hP).symm (Ideal.Quotient.mk P.ideal a) =
      Ideal.Quotient.mk _ ((perfectPrismWittRecoveryEquiv P hP).symm a) := rfl
end OriginalChoices

assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittGenerator
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv_generator
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittGenerator_map_span
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv_symm_map_ideal
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWitt_isAdicComplete_generator
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittQuotientEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittQuotientEquiv_mk
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittQuotientEquiv_symm_mk
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv_symm_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismWittGenerator_isDistinguished
assert_no_sorry SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift
assert_no_sorry SerrePositivity.BhattScholze.OrientedPrism.quotient_isIntegralPerfectoid

#print axioms SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv
#print axioms SerrePositivity.BhattScholze.perfectPrismWittGenerator
#print axioms SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv_generator
#print axioms SerrePositivity.BhattScholze.perfectPrismWittGenerator_map_span
#print axioms SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv_symm_map_ideal
#print axioms SerrePositivity.BhattScholze.perfectPrismWitt_isAdicComplete_generator
#print axioms SerrePositivity.BhattScholze.perfectPrismWittQuotientEquiv
#print axioms SerrePositivity.BhattScholze.perfectPrismWittQuotientEquiv_mk
#print axioms SerrePositivity.BhattScholze.perfectPrismWittQuotientEquiv_symm_mk
#print axioms SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv_symm_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectPrismWittGenerator_isDistinguished
#print axioms SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift
#print axioms SerrePositivity.BhattScholze.OrientedPrism.quotient_isIntegralPerfectoid
end R5BContracts

-- R5c: validated refactoring contracts.
namespace SerrePositivity.BhattScholze.R5CContracts

/- Focused R5c audit: all singleton comparisons, old high-level APIs,
   exact old completion/map, commuting standard-map diagrams,
   and the unrestricted reduced p-adically complete target contract. -/
universe u
section StandardMaps
variable {R : Type u} [CommRing R] (p : ℕ) (ρ : ℕ → R)
example : CompatibleRootCompletion p ρ =
    AdicCompletion (Ideal.span {(p : R ⧸ compatibleRootIdeal ρ)})
      (R ⧸ compatibleRootIdeal ρ) := rfl
example : compatibleRootCompletionMap p ρ =
    (algebraMap (R ⧸ compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)).comp
      (compatibleRootQuotientMap ρ) := rfl
example (r : R) :
    compatibleRootSingletonZeroQuotientEquiv ρ (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl
example (r : R) :
    compatibleRootSingletonQuotientEquiv ρ (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl
example : compatibleRootSingletonCompletionEquiv p ρ =
    RingEquiv.cast (R := fun I : Ideal R ↦
      AdicCompletion (Ideal.span {(p : R ⧸ I)}) (R ⧸ I))
      (compatibleRootFamilyIdeal_singleton ρ) := rfl
example :
    (compatibleRootSingletonQuotientEquiv ρ).toRingHom.comp
        (compatibleRootFamilyQuotientMap (fun _ : PUnit.{u+1} ↦ ρ)) =
      (compatibleRootQuotientMap ρ).comp
        (compatibleRootSingletonZeroQuotientEquiv ρ).toRingHom :=
  compatibleRootSingletonQuotientEquiv_comp_quotientMap ρ
example :
    (compatibleRootSingletonCompletionEquiv p ρ).toRingHom.comp
        (compatibleRootFamilyCompletionMap p (fun _ : PUnit.{u+1} ↦ ρ)) =
      (compatibleRootCompletionMap p ρ).comp
        (compatibleRootSingletonZeroQuotientEquiv ρ).toRingHom :=
  compatibleRootSingletonCompletionEquiv_comp_completionMap p ρ
example (x : R ⧸ compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ)) :
    compatibleRootSingletonCompletionEquiv p ρ (algebraMap _ _ x) =
      algebraMap _ (CompatibleRootCompletion p ρ) (compatibleRootSingletonQuotientEquiv ρ x) :=
  compatibleRootSingletonCompletionEquiv_algebraMap p ρ x
end StandardMaps

section OriginalGeneralTarget
variable {p : ℕ} {R : Type u} [CommRing R]
variable (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
variable {T : Type u} [CommRing T] [IsReduced T]
variable [IsAdicComplete (Ideal.span {(p : T)}) T]
example (g : R ⧸ Ideal.span {ρ 0} →+* T) :
    ∃! l : CompatibleRootCompletion p ρ →+* T,
      l.comp (compatibleRootCompletionMap p ρ) = g :=
  existsUnique_compatibleRootCompletionLift ρ hρ g
end OriginalGeneralTarget

assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal_singleton
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyIdeal_singleton
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootSingletonZeroQuotientEquiv
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootSingletonZeroQuotientEquiv_mk
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootSingletonQuotientEquiv
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootSingletonQuotientEquiv_mk
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootSingletonQuotientEquiv_comp_quotientMap
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootSingletonCompletionEquiv
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootSingletonCompletionEquiv_algebraMap
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootSingletonCompletionEquiv_comp_completionMap
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootCompletion_isIntegralPerfectoid
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootCompletionMap_isPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.surjective_of_isPerfectoidization_of_compatibleRoots_unconditional
assert_no_sorry SerrePositivity.BhattScholze.CompatibleRootCompletion
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootCompletionMap
assert_no_sorry SerrePositivity.BhattScholze.existsUnique_compatibleRootCompletionLift

#print axioms SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal_singleton
#print axioms SerrePositivity.BhattScholze.compatibleRootFamilyIdeal_singleton
#print axioms SerrePositivity.BhattScholze.compatibleRootSingletonZeroQuotientEquiv
#print axioms SerrePositivity.BhattScholze.compatibleRootSingletonZeroQuotientEquiv_mk
#print axioms SerrePositivity.BhattScholze.compatibleRootSingletonQuotientEquiv
#print axioms SerrePositivity.BhattScholze.compatibleRootSingletonQuotientEquiv_mk
#print axioms SerrePositivity.BhattScholze.compatibleRootSingletonQuotientEquiv_comp_quotientMap
#print axioms SerrePositivity.BhattScholze.compatibleRootSingletonCompletionEquiv
#print axioms SerrePositivity.BhattScholze.compatibleRootSingletonCompletionEquiv_algebraMap
#print axioms SerrePositivity.BhattScholze.compatibleRootSingletonCompletionEquiv_comp_completionMap
#print axioms SerrePositivity.BhattScholze.compatibleRootCompletion_isIntegralPerfectoid
#print axioms SerrePositivity.BhattScholze.compatibleRootCompletionMap_isPerfectoidization
#print axioms SerrePositivity.BhattScholze.surjective_of_isPerfectoidization_of_compatibleRoots_unconditional
#print axioms SerrePositivity.BhattScholze.CompatibleRootCompletion
#print axioms SerrePositivity.BhattScholze.compatibleRootCompletionMap
#print axioms SerrePositivity.BhattScholze.existsUnique_compatibleRootCompletionLift
end SerrePositivity.BhattScholze.R5CContracts

-- R6: validated refactoring contracts.
/-! R6 focused audit: 9 new + 1 moved + 18 existing consumer declarations.
These checks supplement the foundation/B4 integration audits. -/

-- New relative Witt lift estimates
assert_no_sorry SerrePositivity.BhattScholze.wittTwoLift_coeff_zero
assert_no_sorry SerrePositivity.BhattScholze.wittTwoLift_delta_add
assert_no_sorry SerrePositivity.BhattScholze.wittTwoLift_delta_mul
assert_no_sorry SerrePositivity.BhattScholze.wittTwoLift_delta_mem_pow
assert_no_sorry SerrePositivity.BhattScholze.wittTwoLift_delta_add_sub_mem_pow
assert_no_sorry SerrePositivity.BhattScholze.wittTwoLift_delta_sub_mem_pow
assert_no_sorry SerrePositivity.BhattScholze.wittTwoLift_map_delta_add_of_left_zero
assert_no_sorry SerrePositivity.BhattScholze.wittTwoLift_map_delta_add_of_right_zero
assert_no_sorry SerrePositivity.BhattScholze.wittTwoLift_map_delta_mul_of_prime_zero

-- Moved carry estimate (same name and type)
assert_no_sorry SerrePositivity.BhattScholze.wittAdditionCarry_mem_of_right_mem

-- Existing consumer API
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.delta_mem_pow
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.delta_add_sub_mem_pow
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.delta_sub_mem_pow
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_mem_pow
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_add_sub_mem_pow
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_sub_mem_pow
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.map_delta_prime_of_zero
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.map_delta_pow_prime_of_zero
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.map_delta_add_of_left_zero
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.map_delta_add_of_right_zero
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.map_delta_mul_of_prime_zero
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteFrobeniusStep_map_of_prime_zero
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_map_mul_of_prime_zero
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_map_add_of_left_zero
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_map_add_of_right_zero
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_map_pow_succ_of_prime_zero
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_map_pow_prime_of_zero
assert_no_sorry SerrePositivity.BhattScholze.relativeFreeFiniteDeltaStep_map_prime_of_zero

-- Axiom review for all new/moved declarations.
#print axioms SerrePositivity.BhattScholze.wittTwoLift_coeff_zero
#print axioms SerrePositivity.BhattScholze.wittTwoLift_delta_add
#print axioms SerrePositivity.BhattScholze.wittTwoLift_delta_mul
#print axioms SerrePositivity.BhattScholze.wittTwoLift_delta_mem_pow
#print axioms SerrePositivity.BhattScholze.wittTwoLift_delta_add_sub_mem_pow
#print axioms SerrePositivity.BhattScholze.wittTwoLift_delta_sub_mem_pow
#print axioms SerrePositivity.BhattScholze.wittTwoLift_map_delta_add_of_left_zero
#print axioms SerrePositivity.BhattScholze.wittTwoLift_map_delta_add_of_right_zero
#print axioms SerrePositivity.BhattScholze.wittTwoLift_map_delta_mul_of_prime_zero
#print axioms SerrePositivity.BhattScholze.wittAdditionCarry_mem_of_right_mem


-- N1: general root-family universality and boundary contracts.

/- Audit of the general family-completion universal property.
   The old declarations and standard maps stay fixed; only the target hypotheses broaden.
   No primality, source completeness, source reducedness, or nonempty index is assumed below. -/
namespace SerrePositivity.BhattScholze.RefactoringFamilyAudit
universe u

section GenericContract
variable {p : ℕ} {R σ T : Type u} [CommRing R] [CommRing T]
variable (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
variable [IsReduced T] [IsAdicComplete (Ideal.span {(p : T)}) T]
example (g : R ⧸ compatibleRootFamilyZeroIdeal ρ →+* T) :
    ∃! l : CompatibleRootFamilyCompletion p ρ →+* T,
      l.comp (compatibleRootFamilyCompletionMap p ρ) = g :=
  existsUnique_compatibleRootFamilyCompletionLift ρ hρ g
end GenericContract

section OldStandardMaps
variable {R σ : Type u} [CommRing R] (p : ℕ) (ρ : σ → ℕ → R)
example : CompatibleRootFamilyCompletion p ρ =
    AdicCompletion (Ideal.span {(p : R ⧸ compatibleRootFamilyIdeal ρ)})
      (R ⧸ compatibleRootFamilyIdeal ρ) := rfl
example : compatibleRootFamilyCompletionMap p ρ =
    (algebraMap (R ⧸ compatibleRootFamilyIdeal ρ) _).comp
      (compatibleRootFamilyQuotientMap ρ) := rfl
example (r : R) : compatibleRootFamilyQuotientMap ρ
    (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ) r) =
      Ideal.Quotient.mk (compatibleRootFamilyIdeal ρ) r := rfl
example (r : R) : compatibleRootFamilyCompletionMap p ρ
    (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ) r) =
      algebraMap (R ⧸ compatibleRootFamilyIdeal ρ) _
        (Ideal.Quotient.mk (compatibleRootFamilyIdeal ρ) r) := rfl
end OldStandardMaps

section EmptyFamily
variable {R T : Type u} [CommRing R] [CommRing T] (p : ℕ)
variable [IsReduced T] [IsAdicComplete (Ideal.span {(p : T)}) T]
example (ρ : PEmpty.{u+1} → ℕ → R) (g : R ⧸ compatibleRootFamilyZeroIdeal ρ →+* T) :
    ∃! l : CompatibleRootFamilyCompletion p ρ →+* T,
      l.comp (compatibleRootFamilyCompletionMap p ρ) = g :=
  existsUnique_compatibleRootFamilyCompletionLift ρ (fun s => PEmpty.elim s) g
example (ρ : PEmpty.{u+1} → ℕ → R) : compatibleRootFamilyZeroIdeal ρ = ⊥ := by
  change Ideal.span (Set.range (fun s => ρ s 0)) = ⊥
  simp
example (ρ : PEmpty.{u+1} → ℕ → R) : compatibleRootFamilyIdeal ρ = ⊥ := by
  change Ideal.span (Set.range (fun x : PEmpty.{u+1} × ℕ => ρ x.1 x.2)) = ⊥
  simp
end EmptyFamily

/- A composite completion parameter with a nontrivial reduced complete target.
   Fact 2.Prime is a target-ring fact; no Fact 4.Prime is introduced. -/
example (g : ZMod 2 ⧸ compatibleRootFamilyZeroIdeal
    (fun (_ : PUnit) (_ : ℕ) => (0 : ZMod 2)) →+* ZMod 2) :
    ∃! l : CompatibleRootFamilyCompletion 4
        (fun (_ : PUnit) (_ : ℕ) => (0 : ZMod 2)) →+* ZMod 2,
      l.comp (compatibleRootFamilyCompletionMap 4
        (fun (_ : PUnit) (_ : ℕ) => (0 : ZMod 2))) = g := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsAdicComplete (Ideal.span {(4 : ZMod 2)}) (ZMod 2) := by
    have hz : (4 : ZMod 2) = 0 := by decide
    rw [hz, Ideal.span_singleton_zero]
    infer_instance
  exact existsUnique_compatibleRootFamilyCompletionLift _ (by intros; simp) g

/- Parameter zero, empty family, and an ordinary reduced target: no source
   precompleteness or prime assumption is available. -/
example {R : Type} [CommRing R] (ρ : PEmpty → ℕ → R)
    (g : R ⧸ compatibleRootFamilyZeroIdeal ρ →+* ℤ) :
    ∃! l : CompatibleRootFamilyCompletion 0 ρ →+* ℤ,
      l.comp (compatibleRootFamilyCompletionMap 0 ρ) = g := by
  let : IsAdicComplete (Ideal.span {(0 : ℤ)}) ℤ := by
    rw [Ideal.span_singleton_zero]
    infer_instance
  exact existsUnique_compatibleRootFamilyCompletionLift ρ (fun s => PEmpty.elim s) g

/- A literal zero source and target with arbitrary p, including p = 1. -/
example {σ : Type u} (p : ℕ) (ρ : σ → ℕ → PUnit.{u+1})
    (g : PUnit.{u+1} ⧸ compatibleRootFamilyZeroIdeal ρ →+* PUnit.{u+1}) :
    ∃! l : CompatibleRootFamilyCompletion p ρ →+* PUnit.{u+1},
      l.comp (compatibleRootFamilyCompletionMap p ρ) = g := by
  let : IsReduced PUnit.{u+1} := ⟨fun _ _ => Subsingleton.elim _ _⟩
  exact existsUnique_compatibleRootFamilyCompletionLift ρ
    (fun _ _ => Subsingleton.elim _ _) g

#check @existsUnique_compatibleRootFamilyCompletionLift
#print axioms existsUnique_compatibleRootFamilyCompletionLift
#print axioms existsUnique_compatibleRootFamilyCompletionLift_to_perfectoid
#print axioms compatibleRootFamilyCompletionMap_isPerfectoidization_of_isIntegralPerfectoid

end SerrePositivity.BhattScholze.RefactoringFamilyAudit

assert_no_sorry SerrePositivity.BhattScholze.existsUnique_compatibleRootFamilyCompletionLift
assert_no_sorry SerrePositivity.BhattScholze.existsUnique_compatibleRootFamilyCompletionLift_to_perfectoid
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyCompletionMap_isPerfectoidization_of_isIntegralPerfectoid

-- N2: reuse the existing p-ideal map formula, preserving all four public entrances.

assert_no_sorry SerrePositivity.BhattScholze.compatibleRootCompletion_isAdicComplete
#print axioms SerrePositivity.BhattScholze.compatibleRootCompletion_isAdicComplete
assert_no_sorry SerrePositivity.BhattScholze.exists_compatibleRootCompletionPDQuotientEquiv
#print axioms SerrePositivity.BhattScholze.exists_compatibleRootCompletionPDQuotientEquiv
assert_no_sorry SerrePositivity.BhattScholze.compatibleRootFamilyCompletion_isAdicComplete
#print axioms SerrePositivity.BhattScholze.compatibleRootFamilyCompletion_isAdicComplete
assert_no_sorry SerrePositivity.BhattScholze.exists_compatibleRootFamilyCompletionPDQuotientEquiv
#print axioms SerrePositivity.BhattScholze.exists_compatibleRootFamilyCompletionPDQuotientEquiv

-- N5/N7: all ten old public declarations, including both actual single comparisons.
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismRootSource_powerCokernel_homology_isZero
#print axioms SerrePositivity.BhattScholze.perfectPrismRootSource_powerCokernel_homology_isZero
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismRootSource_pure
#print axioms SerrePositivity.BhattScholze.perfectPrismRootSource_pure
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismRootSource_homology_isZero
#print axioms SerrePositivity.BhattScholze.perfectPrismRootSource_homology_isZero
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismRootSourceSingleIso
#print axioms SerrePositivity.BhattScholze.perfectPrismRootSourceSingleIso
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismRootSourceSingleIso_homologyZero
#print axioms SerrePositivity.BhattScholze.perfectPrismRootSourceSingleIso_homologyZero
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion
#print axioms SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletionPower_homology_isZero
#print axioms SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletionPower_homology_isZero
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletion_powerCokernel_homology_isZero
#print axioms SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletion_powerCokernel_homology_isZero
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletion_pure
#print axioms SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletion_pure
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletionSingleIso
#print axioms SerrePositivity.BhattScholze.perfectPrismDeltaAlgebraCompletionSingleIso

namespace SerrePositivity.BhattScholze.RefactoringMilnorAudit
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section RootSingle
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "X" => DeltaRootSourceIteratedPDCompletion P.deltaStructure P.generator b

-- The original source itself remains both nonnegative and nonpositive.
example : (X).obj.IsGE 0 ∧ (X).obj.IsLE 0 := perfectPrismRootSource_pure P hP b

-- The existing single comparison is normalized on the same H0, not an arbitrary iso.
example :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (perfectPrismRootSourceSingleIso P hP b).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).hom.app
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (X).obj) = 𝟙 _ :=
  perfectPrismRootSourceSingleIso_homologyZero P hP b
end RootSingle

section DeltaSingle
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (E : DeltaStructure p B) (j : A →+* B)
variable (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
variable
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j P.generator

-- All original coefficient-ring, delta-map, mod-(p,d) and faithful-flat inputs are retained.
example : (X).obj.IsGE 0 ∧ (X).obj.IsLE 0 :=
  perfectPrismDeltaAlgebraCompletion_pure P E j hP hj hzero hFF

-- The second existing single comparison has the same normalization as the root source.
example :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (perfectPrismDeltaAlgebraCompletionSingleIso P E j hP hj hzero hFF).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).hom.app
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (X).obj) = 𝟙 _ := by
  obtain ⟨hGE, hLE⟩ := perfectPrismDeltaAlgebraCompletion_pure P E j hP hj hzero hFF
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso_homology (X).obj 0
end DeltaSingle

end
end SerrePositivity.BhattScholze.RefactoringMilnorAudit

-- N4: all nine old public declarations; local coefficient actions stay explicit.
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteSupportTransition
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteSupportTransition
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteSupportTransition_mk
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteSupportTransition_mk
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteSupportModuleDiagram
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteSupportModuleDiagram
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteSupportEval
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteSupportEval
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteSupportEval_mk
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteSupportEval_mk
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteSupportEvalCocone
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteSupportEvalCocone
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteSupportEvalIsColimit
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteSupportEvalIsColimit
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteSupportColimitEvalIso
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteSupportColimitEvalIso
assert_no_sorry SerrePositivity.BhattScholze.deltaDivisionFiniteSupportColimitEvalIso_ι
#print axioms SerrePositivity.BhattScholze.deltaDivisionFiniteSupportColimitEvalIso_ι

namespace SerrePositivity.BhattScholze.RefactoringFiniteSupportAudit
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section FiniteSupport
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "K" => deltaDivisionEvaluationFiniteSupportIdeal D a

example (S : Finset (σ × ℕ)) :
    (deltaDivisionFiniteSupportModuleDiagram D a).obj S = ModuleCat.of L (L ⧸ K S) := rfl

example {S T : Finset (σ × ℕ)} (h : S ⊆ T) :
    (deltaDivisionFiniteSupportModuleDiagram D a).map (homOfLE h) =
      ModuleCat.ofHom (deltaDivisionFiniteSupportTransition D a h) := rfl

example {S T : Finset (σ × ℕ)} (h : S ⊆ T) (r : L) :
    deltaDivisionFiniteSupportTransition D a h (Ideal.Quotient.mk (K S) r) =
      Ideal.Quotient.mk (K T) r := rfl

example (S : Finset (σ × ℕ)) (r : L) :
    let := deltaDivisionSourceEvaluationAlgebra D a
    deltaDivisionFiniteSupportEval D a S (Ideal.Quotient.mk (K S) r) =
      deltaDivisionSourceEval D a r := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  rfl

-- This detects changing the local L-action on A to an unrelated algebra instance.
example (S : Finset (σ × ℕ)) (r : L) (x : L ⧸ K S) :
    let := deltaDivisionSourceEvaluationAlgebra D a
    deltaDivisionFiniteSupportEval D a S (r • x) =
      deltaDivisionSourceEval D a r * deltaDivisionFiniteSupportEval D a S x := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  exact (deltaDivisionFiniteSupportEval D a S).map_smul r x

example :
    let := deltaDivisionSourceEvaluationAlgebra D a
    IsColimit (deltaDivisionFiniteSupportEvalCocone D a) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  exact deltaDivisionFiniteSupportEvalIsColimit D a

-- Compare each original colimit injection with the actual beta-evaluation map.
example (S : Finset (σ × ℕ)) :
    let := deltaDivisionSourceEvaluationAlgebra D a
    colimit.ι (deltaDivisionFiniteSupportModuleDiagram D a) S ≫
      (deltaDivisionFiniteSupportColimitEvalIso D a).hom =
        ModuleCat.ofHom (deltaDivisionFiniteSupportEval D a S) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  exact deltaDivisionFiniteSupportColimitEvalIso_ι D a S
end FiniteSupport


section BoundedSupport
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)

-- Cofinal restriction still has the original beta-evaluation target and each standard leg.
example (S : Finset (σ × ℕ)) :
    let := deltaDivisionSourceEvaluationAlgebra D a
    colimit.ι (deltaDivisionBoundedSupportModuleDiagram D a) S ≫
      (deltaDivisionBoundedSupportColimitEvalIso D a).hom =
        ModuleCat.ofHom (deltaDivisionFiniteSupportEval D a (deltaDivisionCoordinateHull S)) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  exact deltaDivisionBoundedSupportColimitEvalIso_ι D a S

-- No nonempty-family or nontrivial-ring assumption is required.
example :
    let := deltaDivisionSourceEvaluationAlgebra D a
    IsColimit (deltaDivisionBoundedSupportEvalCocone D a) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  exact deltaDivisionBoundedSupportEvalIsColimit D a
end BoundedSupport

section BoundedSupportTor
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) a
local notation "I" => Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk (R := L) I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
local notation "F" => deltaDivisionBoundedSupportModuleDiagram E r

-- Keep the original residue map and explicit preservation hypothesis in the public consumer.
example (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ)
    (hpres : PreservesColimit F ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    let := deltaDivisionSourceEvaluationAlgebra E r
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  exact deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit D d a hpA v hv i hpres
end BoundedSupportTor

section BoundaryCases
variable {p : ℕ} [Fact p.Prime]

-- Empty finite support creates no relation; do not strengthen the indexed diagram.
example {A σ : Type u} [CommRing A] (D : DeltaStructure p A) (a : σ → A) :
    deltaDivisionEvaluationFiniteSupportIdeal D a (∅ : Finset (σ × ℕ)) = ⊥ := by
  simp [deltaDivisionEvaluationFiniteSupportIdeal]

-- An empty family is allowed, with no Nonempty or Fintype assumption on the old API.
example {A : Type u} [CommRing A] (D : DeltaStructure p A) :
    let a : PEmpty.{u + 1} → A := fun s => nomatch s
    let := deltaDivisionSourceEvaluationAlgebra D a
    IsColimit (deltaDivisionFiniteSupportEvalCocone D a) := by
  let a : PEmpty.{u + 1} → A := fun s => nomatch s
  let := deltaDivisionSourceEvaluationAlgebra D a
  exact deltaDivisionFiniteSupportEvalIsColimit D a

-- A zero coefficient ring is allowed for any family, with the delta structure explicit.
example {σ : Type u} (D : DeltaStructure p PUnit.{u + 1}) (a : σ → PUnit.{u + 1}) :
    let := deltaDivisionSourceEvaluationAlgebra D a
    IsColimit (deltaDivisionFiniteSupportEvalCocone D a) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  exact deltaDivisionFiniteSupportEvalIsColimit D a
end BoundaryCases

end
end SerrePositivity.BhattScholze.RefactoringFiniteSupportAudit

-- N7: the direct common purity criterion retains the old boundary cases.
namespace SerrePositivity.BhattScholze.RefactoringScalarPurityAudit
noncomputable section
universe u
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime]

example {A : Type u} [CommRing A] (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) :
    let b : PEmpty.{u + 1} → A := fun s => nomatch s
    let X := DeltaRootSourceIteratedPDCompletion P.deltaStructure P.generator b
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let b : PEmpty.{u + 1} → A := fun s => nomatch s
  exact perfectPrismRootSource_pure P hP b

example {σ : Type u} (P : OrientedPrism p PUnit.{u + 1})
    (hP : P.deltaStructure.IsPerfect) (b : σ → PUnit.{u + 1}) :
    let X := DeltaRootSourceIteratedPDCompletion P.deltaStructure P.generator b
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 :=
  perfectPrismRootSource_pure P hP b

end
end SerrePositivity.BhattScholze.RefactoringScalarPurityAudit

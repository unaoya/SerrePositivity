import SerrePositivity.BhattScholze.Andre.MonicRootedExtension
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.Andre.adjoinRoot_faithfullyFlat
assert_no_sorry SerrePositivity.BhattScholze.Andre.exists_monicRootedFaithfullyFlat
assert_no_sorry SerrePositivity.BhattScholze.Andre.expandedPower_quotient_free_faithfullyFlat
assert_no_sorry SerrePositivity.BhattScholze.Andre.monicRelation
assert_no_sorry SerrePositivity.BhattScholze.Andre.monicRelation_isSMulRegular

assert_no_sorry SerrePositivity.BhattScholze.Andre.DivisionPrismCarrier
assert_no_sorry SerrePositivity.BhattScholze.Andre.divisionPrismCommRing
assert_no_sorry SerrePositivity.BhattScholze.Andre.divisionPrism
assert_no_sorry SerrePositivity.BhattScholze.Andre.divisionPrism_isPerfect
assert_no_sorry SerrePositivity.BhattScholze.Andre.DivisionPerfectoidCandidate
assert_no_sorry SerrePositivity.BhattScholze.Andre.divisionPerfectoidCandidate_isIntegralPerfectoid
assert_no_sorry SerrePositivity.BhattScholze.Andre.divisionPerfectoidCandidateMap
assert_no_sorry SerrePositivity.BhattScholze.Andre.divisionPerfectoidCandidateMap_d
assert_no_sorry SerrePositivity.BhattScholze.Andre.divisionPerfectoidCandidateMap_relation
assert_no_sorry SerrePositivity.BhattScholze.Andre.divisionPerfectoidCandidateBaseMap
assert_no_sorry SerrePositivity.BhattScholze.Andre.polynomialPrismCommRing
assert_no_sorry SerrePositivity.BhattScholze.Andre.PolynomialPerfectoidCandidate
assert_no_sorry SerrePositivity.BhattScholze.Andre.polynomialPerfectoidCandidateCoefficientMap
assert_no_sorry SerrePositivity.BhattScholze.Andre.polynomialPerfectoidCandidateRoot
assert_no_sorry SerrePositivity.BhattScholze.Andre.polynomialPerfectoidCandidate_isIntegralPerfectoid
assert_no_sorry SerrePositivity.BhattScholze.Andre.polynomialPerfectoidCandidate_eval
assert_no_sorry SerrePositivity.BhattScholze.Andre.polynomialPerfectoidCandidateCoefficientMap_d
assert_no_sorry SerrePositivity.BhattScholze.Andre.polynomialPerfectoidCandidateBaseMap
assert_no_sorry SerrePositivity.BhattScholze.Andre.perfectPrismMonicLift
assert_no_sorry SerrePositivity.BhattScholze.Andre.perfectPrismMonicLift_map
assert_no_sorry SerrePositivity.BhattScholze.Andre.perfectPrismMonicLift_spec
assert_no_sorry SerrePositivity.BhattScholze.Andre.exists_monicRootedPerfectoidCandidate_of_perfectPrism
assert_no_sorry SerrePositivity.BhattScholze.Andre.evaluatedDP_quotient_free
assert_no_sorry SerrePositivity.BhattScholze.Andre.principalDPPresentation_quotient_free
assert_no_sorry SerrePositivity.BhattScholze.Andre.monicDPPresentation_free
assert_no_sorry SerrePositivity.BhattScholze.Andre.principalDPPresentation_faithfullyFlat_of_quotient
assert_no_sorry SerrePositivity.BhattScholze.Andre.monicDPPresentation_faithfullyFlat
assert_no_sorry SerrePositivity.BhattScholze.Andre.expandedMonicDPPresentation_faithfullyFlat

-- 本レーンの各宣言（生成された宣言も含む）の推移的な公理依存を検査する。
open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.BhattScholze.Andre.OrdinaryMonicRoot,
    `SerrePositivity.BhattScholze.Andre.MonicRelation,
    `SerrePositivity.BhattScholze.Andre.DivisionPerfectoidCandidate,
    `SerrePositivity.BhattScholze.Andre.PolynomialPerfectoidCandidate,
    `SerrePositivity.BhattScholze.Andre.PerfectPrismMonicCandidate,
    `SerrePositivity.BhattScholze.Andre.PrincipalDPFree,
    `SerrePositivity.BhattScholze.Andre.MonicPDFlat]
  let mut seen : Array Name := #[]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  unless seen.size == expected.size do
    throwError "Missing André monic root modules"
  logInfo m!"André monic root audit passed: {count} declarations, standard axioms only."

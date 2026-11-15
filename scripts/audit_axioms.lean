-- lake build の後、lake env lean scripts/audit_axioms.lean で実行する。
import SerrePositivity
import Mathlib.Util.PrintSorries
import Mathlib.Util.AssertNoSorry
#print axioms SerrePositivity.lengthNat_add_of_exact
#print axioms SerrePositivity.Section2.towerLengthFun_eq_fgLength
#print axioms SerrePositivity.Section2.towerLengthFun_tensor
#print axioms SerrePositivity.lengthNat_ker_add_range
#print axioms SerrePositivity.lengthNat_eq_add_range
#print axioms SerrePositivity.lengthInt_eq_add_range
#print axioms SerrePositivity.lengthEuler_longExact
#print axioms SerrePositivity.lengthEuler_finsum_longExact
#print axioms SerrePositivity.alternatingFinsum_add_one
#print axioms SerrePositivity.alternatingFinsum_eq_of_boundary
#print axioms SerrePositivity.alternatingSum_range_exact
#print axioms SerrePositivity.coneLength_pow_of_recurrence
#print axioms SerrePositivity.iteratedScalarCone_smul_zero_of_smul_zero
#print axioms SerrePositivity.homotopyKoszulObj
#print axioms SerrePositivity.homotopyKoszulTriangle
#print axioms SerrePositivity.homotopyKoszulTriangle_mk_distinguished
#print axioms SerrePositivity.koszulComplexOn_smul_zero
#print axioms SerrePositivity.lambdaHomology_koszul_null_finite
#print axioms SerrePositivity.lambdaHomology_koszul_null_pow
#print axioms SerrePositivity.lambdaHomology_koszul_null_binomial
#print axioms SerrePositivity.ordinary_koszulEuler_eq_koszulEulerChar
#print axioms SerrePositivity.regularResolution
#print axioms SerrePositivity.isWeaklyRegular_of_span_eq_maximalIdeal
#print axioms SerrePositivity.ringKrullDim_quotient_add_length_of_mem_associatedPrimes
#print axioms SerrePositivity.koszulEulerChar_eq_finrank
#print axioms SerrePositivity.KoszulMultiplicity.termLength_cone_of_finite
#print axioms SerrePositivity.KoszulMultiplicity.euler_cone_of_finite
#print axioms SerrePositivity.KoszulMultiplicity.termLength_cone
#print axioms SerrePositivity.KoszulMultiplicity.euler_cone
#print axioms SerrePositivity.AdicFilteredComplex.quasiIso_projection
#print axioms SerrePositivity.AdicFilteredComplex.finiteLength_quotient_term
#print axioms SerrePositivity.FiniteLengthComplexEuler.shortComplex_length_identity
#print axioms SerrePositivity.FiniteLengthComplexEuler.chiOrd_eq_alternating_term_lengths
#print axioms SerrePositivity.HilbertSerre.component_length_identity
#print axioms SerrePositivity.LengthAlgebra.perfectEuler_conjSum_eq
#print axioms SerrePositivity.Section4.symmetricPaperEuler_conjSum_eq
#print axioms SerrePositivity.KoszulMultiplicity.multiplicity_eq_chiOrd_koszul
#print axioms SerrePositivity.lemma_3_5
#print axioms SerrePositivity.Section4.theorem_4_7_K0
#print axioms SerrePositivity.Section2.theorem_2_5
#print axioms SerrePositivity.core_statement
#print axioms SerrePositivity.main_statement
#print sorries SerrePositivity.main_statement

-- 共通層・仮定確認・標準可換環論には未証明依存を認めない。
assert_no_sorry SerrePositivity.lengthNat_add_of_exact
assert_no_sorry SerrePositivity.Section2.towerLengthFun_eq_fgLength
assert_no_sorry SerrePositivity.Section2.towerLengthFun_tensor
assert_no_sorry SerrePositivity.lengthNat_ker_add_range
assert_no_sorry SerrePositivity.lengthNat_eq_add_range
assert_no_sorry SerrePositivity.lengthInt_eq_add_range
assert_no_sorry SerrePositivity.lengthEuler_longExact
assert_no_sorry SerrePositivity.lengthEuler_finsum_longExact
assert_no_sorry SerrePositivity.alternatingFinsum_add_one
assert_no_sorry SerrePositivity.alternatingFinsum_eq_of_boundary
assert_no_sorry SerrePositivity.alternatingSum_range_exact
assert_no_sorry SerrePositivity.coneLength_pow_of_recurrence
assert_no_sorry SerrePositivity.iteratedScalarCone_smul_zero_of_smul_zero
assert_no_sorry SerrePositivity.homotopyKoszulObj
assert_no_sorry SerrePositivity.homotopyKoszulTriangle
assert_no_sorry SerrePositivity.homotopyKoszulTriangle_mk_distinguished
assert_no_sorry SerrePositivity.koszulComplexOn_smul_zero
assert_no_sorry SerrePositivity.lambdaHomology_koszul_null_finite
assert_no_sorry SerrePositivity.lambdaHomology_koszul_null_pow
assert_no_sorry SerrePositivity.lambdaHomology_koszul_null_binomial
assert_no_sorry SerrePositivity.ordinary_koszulEuler_eq_koszulEulerChar
assert_no_sorry SerrePositivity.regularResolution
assert_no_sorry SerrePositivity.isWeaklyRegular_of_span_eq_maximalIdeal
assert_no_sorry SerrePositivity.ringKrullDim_quotient_add_length_of_mem_associatedPrimes
assert_no_sorry SerrePositivity.koszulEulerChar_eq_finrank
assert_no_sorry SerrePositivity.KoszulMultiplicity.termLength_cone_of_finite
assert_no_sorry SerrePositivity.KoszulMultiplicity.euler_cone_of_finite
assert_no_sorry SerrePositivity.KoszulMultiplicity.termLength_cone
assert_no_sorry SerrePositivity.KoszulMultiplicity.euler_cone
assert_no_sorry SerrePositivity.AdicFilteredComplex.quasiIso_projection
assert_no_sorry SerrePositivity.AdicFilteredComplex.finiteLength_quotient_term
assert_no_sorry SerrePositivity.FiniteLengthComplexEuler.shortComplex_length_identity
assert_no_sorry SerrePositivity.FiniteLengthComplexEuler.chiOrd_eq_alternating_term_lengths
assert_no_sorry SerrePositivity.HilbertSerre.component_length_identity
assert_no_sorry SerrePositivity.LengthAlgebra.perfectEuler_conjSum_eq
assert_no_sorry SerrePositivity.Section4.symmetricPaperEuler_conjSum_eq
assert_no_sorry SerrePositivity.KoszulMultiplicity.multiplicity_eq_chiOrd_koszul

-- 引用1の型を保った実構成と、その剰余体還元への適用。
#print axioms SerrePositivity.exists_complete_flat_local_extension_of_residueField
assert_no_sorry SerrePositivity.exists_complete_flat_local_extension_of_residueField
#print axioms SerrePositivity.Section2.lemma_2_1
assert_no_sorry SerrePositivity.Section2.lemma_2_1

-- 引用3の既存型を保持した混標数Cohen正規化の実構成。
#print axioms SerrePositivity.exists_cohen_normalization_mixedCharacteristic
assert_no_sorry SerrePositivity.exists_cohen_normalization_mixedCharacteristic

-- 標準完備塔の旧Inputs入口は実際のtiltとFontaine核から証明済み。
#print axioms SerrePositivity.Section2.completedTower_isIntegralPerfectoid_of_standard_wittPresentation
assert_no_sorry SerrePositivity.Section2.completedTower_isIntegralPerfectoid_of_standard_wittPresentation

-- 剰余標数零の Serre の正値性：対角線論法の核と、その部品は標準公理のみ。
#print axioms SerrePositivity.DiagonalRing.chi_pos_of_prime
assert_no_sorry SerrePositivity.DiagonalRing.chi_pos_of_prime
#print axioms SerrePositivity.flat_of_isWeaklyRegular
assert_no_sorry SerrePositivity.flat_of_isWeaklyRegular
#print axioms SerrePositivity.exists_mvPowerSeries_ringEquiv_of_charZero
assert_no_sorry SerrePositivity.exists_mvPowerSeries_ringEquiv_of_charZero
-- 交点消滅は巡回 Adams 作用素で全剰余標数にわたり証明済み。
#print axioms SerrePositivity.intersectionVanishing_of_adams
assert_no_sorry SerrePositivity.intersectionVanishing_of_adams
-- 一般の剰余標数零の正値性も、デヴィサージュと証明済みの消滅により標準公理のみ。
#print axioms SerrePositivity.chi_pos_of_residueCharZero
assert_no_sorry SerrePositivity.chi_pos_of_residueCharZero

-- Cohen–Gabberの公開型を保った微分経路の実構成。
#print axioms SerrePositivity.exists_cohen_gabber_normalization
assert_no_sorry SerrePositivity.exists_cohen_gabber_normalization
#print axioms SerrePositivity.Section2.lemma_2_2
assert_no_sorry SerrePositivity.Section2.lemma_2_2

-- The main theorem may retain separately audited inputs, but the old B-S citation must not return.
meta section
open Lean Elab Command
private partial def checkNoLegacySurjectivity (todo : List Name) (seen : NameSet) : CoreM Unit := do
  match todo with
  | [] => return
  | n :: rest =>
    if seen.contains n then return ← checkNoLegacySurjectivity rest seen
    if n == `SerrePositivity.BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotient ||
        n == `SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_complete_torsionFree_quotient then
      throwError "Main theorem reached the legacy B-S surjectivity citation: {n}"
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkNoLegacySurjectivity rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    checkNoLegacySurjectivity (deps.toList ++ rest) seen

elab "assert_main_no_legacy_surjectivity" : command => do
  liftCoreM <| checkNoLegacySurjectivity [``SerrePositivity.main_statement] {}
  logInfo "Main theorem: legacy B-S surjectivity citation absent."
end

assert_main_no_legacy_surjectivity

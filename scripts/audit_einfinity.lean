import SerrePositivity.EInfinity
import Lean.Util.CollectAxioms

-- EInfinity の全宣言の推移的な公理依存を監査する。
open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.EInfinity).isPrefixOf mod do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax ↦
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "非標準公理への依存: {name}: {unexpected}"
    declarations := declarations + 1
  if declarations == 0 then throwError "監査対象の EInfinity 宣言がありません"
  unless env.contains `SerrePositivity.EInfinity.projectiveModelCategory do
    throwError "射影モデル構造の宣言がありません"
  for required in #[`SerrePositivity.EInfinity.BarrattEccles.operad,
      `SerrePositivity.EInfinity.BarrattEccles.augmentation,
      `SerrePositivity.EInfinity.BarrattEccles.augmentation_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.complexContraction,
      `SerrePositivity.EInfinity.BarrattEccles.equivariantBasis_rightAction,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonalDegree_eq_sum,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_projection,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_natural,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_coassoc,
      `SerrePositivity.EInfinity.AlexanderWhitney.counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_left_counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_right_counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.counit_natural,
      `SerrePositivity.EInfinity.NegativeTensor.comparison,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_natural,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_associator,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_leftUnitor,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_rightUnitor,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_projection_generator,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_coassoc,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_left_counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_right_counit,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_rightAction,
      `SerrePositivity.EInfinity.BarrattEccles.cochainCounit_eq_augmentation,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_coassoc,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_left_counit,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_right_counit,
      `SerrePositivity.EInfinity.Shuffle.simplex_σ_left,
      `SerrePositivity.EInfinity.Shuffle.simplex_σ_right,
      `SerrePositivity.EInfinity.Shuffle.normalizedBilinear_normalization,
      `SerrePositivity.EInfinity.Shuffle.component,
      `SerrePositivity.EInfinity.Shuffle.component_generators,
      `SerrePositivity.EInfinity.Shuffle.component_natural,
      `SerrePositivity.EInfinity.Shuffle.frontPath,
      `SerrePositivity.EInfinity.Shuffle.backPath,
      `SerrePositivity.EInfinity.Shuffle.simplex_frontCut,
      `SerrePositivity.EInfinity.Shuffle.simplex_backCut,
      `SerrePositivity.EInfinity.Shuffle.aw_component_simplex,
      `SerrePositivity.EInfinity.Shuffle.pathCutEquiv,
      `SerrePositivity.EInfinity.Shuffle.sign_eq_pow_inversionNumber,
      `SerrePositivity.EInfinity.Shuffle.inversionNumber_edgeJoin,
      `SerrePositivity.EInfinity.Shuffle.pathCut_sign,
      `SerrePositivity.EInfinity.Shuffle.signed_sum_pathCut,
      `SerrePositivity.EInfinity.Shuffle.diagonal_value_split_sum,
      `SerrePositivity.EInfinity.Shuffle.diagonal_value,
      `SerrePositivity.EInfinity.Shuffle.component_diagonal,
      `SerrePositivity.EInfinity.Shuffle.simplex_horizontal_face,
      `SerrePositivity.EInfinity.Shuffle.simplex_vertical_face,
      `SerrePositivity.EInfinity.Shuffle.sum_mixedBoundary_eq_zero,
      `SerrePositivity.EInfinity.Shuffle.shuffleBilinear_d_positive,
      `SerrePositivity.EInfinity.Shuffle.shuffleBilinear_d_leftZero,
      `SerrePositivity.EInfinity.Shuffle.shuffleBilinear_d_rightZero,
      `SerrePositivity.EInfinity.Shuffle.component_d_positive,
      `SerrePositivity.EInfinity.Shuffle.degreeMap_d,
      `SerrePositivity.EInfinity.Shuffle.chainMap,
      `SerrePositivity.EInfinity.Shuffle.ι_chainMap,
      `SerrePositivity.EInfinity.Shuffle.chainMap_natural,
      `SerrePositivity.EInfinity.Shuffle.chainMap_generators,
      `SerrePositivity.EInfinity.NatTensor.shapeSymmetry,
      `SerrePositivity.EInfinity.NatTensor.symmetry,
      `SerrePositivity.EInfinity.NatTensor.interchange,
      `SerrePositivity.EInfinity.NatTensor.inclusion_interchange,
      `SerrePositivity.EInfinity.Shuffle.chainMap_diagonal,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_symmetry,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_interchange,
      `SerrePositivity.EInfinity.NegativeTensor.binaryMap_comultiplication,
      `SerrePositivity.EInfinity.Shuffle.cochainMap_diagonal,
      `SerrePositivity.EInfinity.BarrattEccles.simplicialPartialComposition,
      `SerrePositivity.EInfinity.BarrattEccles.partialComposition_eq_generalShuffle,
      `SerrePositivity.EInfinity.BarrattEccles.partialComposition_diagonal_tensorμ,
      `SerrePositivity.EInfinity.Operad.hadamard,
      `SerrePositivity.EInfinity.Operad.Hadamard.separate_swap,
      `SerrePositivity.EInfinity.Operad.Hadamard.nested_assoc,
      `SerrePositivity.EInfinity.Operad.Hadamard.parallel_assoc,
      `SerrePositivity.EInfinity.Operad.Hopf,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_vertex,
      `SerrePositivity.EInfinity.BarrattEccles.unit_diagonal,
      `SerrePositivity.EInfinity.BarrattEccles.hopfDiagonal,
      `SerrePositivity.EInfinity.BarrattEccles.hopf,
      `SerrePositivity.EInfinity.tensorCoInsertionAction,
      `SerrePositivity.EInfinity.tensorCoInsertionAction_coeff,
      `SerrePositivity.EInfinity.tensorCoComposition_coeff,
      `SerrePositivity.EInfinity.Operad.Coalgebra,
      `SerrePositivity.EInfinity.Operad.CoalgebraHom,
      `SerrePositivity.EInfinity.Operad.Coalgebra.forget,
      `SerrePositivity.EInfinity.Operad.restrictCoalgebra,
      `SerrePositivity.EInfinity.tensorUnitPowerIso_append,
      `SerrePositivity.EInfinity.tensorUnitPower_permutation,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.endpoint_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.restrict,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_post,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_pre,
      `SerrePositivity.EInfinity.Operad.convolutionAction,
      `SerrePositivity.EInfinity.Operad.convolutionAction_uncurry,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.prepathComplex,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.constantNat,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationNat,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_one,
      `SerrePositivity.EInfinity.convolutionUnitLaw,
      `SerrePositivity.EInfinity.Operad.convolutionAction_unit,
      `SerrePositivity.EInfinity.tensorPowerSeparation,
      `SerrePositivity.EInfinity.tensorPowerSeparation_permutation,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_separation,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_permutation,
      `SerrePositivity.EInfinity.convolutionAssembly_naturality,
      `SerrePositivity.EInfinity.Operad.convolutionAction_equivariance,
      `SerrePositivity.EInfinity.Operad.convolutionAction_post,
      `SerrePositivity.EInfinity.tensorSeparation_twice,
      `SerrePositivity.EInfinity.tensorPowerSeparation_append,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_index,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_append,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_split,
      `SerrePositivity.EInfinity.tensorCoInsertionAction_zero,
      `SerrePositivity.EInfinity.tensorInsertionAction_zero_append,
      `SerrePositivity.EInfinity.convolutionAssembly_transport,
      `SerrePositivity.EInfinity.convolutionAssembly_tensorRight,
      `SerrePositivity.EInfinity.Operad.Algebra.comp_action_of_first,
      `SerrePositivity.EInfinity.Operad.Algebra.ofFirstComposition,
      `SerrePositivity.EInfinity.Operad.convolutionAction_firstBlock_evaluation,
      `SerrePositivity.EInfinity.Operad.convolutionAction_insertion_zero_evaluation,
      `SerrePositivity.EInfinity.Operad.Hopf.diagonalComponent,
      `SerrePositivity.EInfinity.convolutionAssembly_composition,
      `SerrePositivity.EInfinity.convolutionAssembly_composition_of_maps,
      `SerrePositivity.EInfinity.convolutionAssembly_pre,
      `SerrePositivity.EInfinity.Operad.convolutionUncurriedAction_comp_zero,
      `SerrePositivity.EInfinity.Operad.convolutionAction_comp_zero,
      `SerrePositivity.EInfinity.Operad.convolutionAction_comp,
      `SerrePositivity.EInfinity.Operad.convolutionAlgebra,
      `SerrePositivity.EInfinity.Operad.convolutionAction_pre,
      `SerrePositivity.EInfinity.Operad.convolutionFunctor,
      `SerrePositivity.EInfinity.Operad.convolutionPreNat,
      `SerrePositivity.EInfinity.tensorUnitPowerIso_split,
      `SerrePositivity.EInfinity.tensorCoInsertionAction_unit,
      `SerrePositivity.EInfinity.Operad.unitCoaction_equivariance,
      `SerrePositivity.EInfinity.Operad.unitCoaction_unit,
      `SerrePositivity.EInfinity.Operad.unitCoaction_partialComposition,
      `SerrePositivity.EInfinity.Operad.unitCoalgebra,
      `SerrePositivity.EInfinity.Operad.Algebra.isoOfCarrierIso,
      `SerrePositivity.EInfinity.convolutionEvaluation_unit_source,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_unit_source,
      `SerrePositivity.EInfinity.Operad.convolutionUnitIso,
      `SerrePositivity.EInfinity.Operad.convolutionUnitNatIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.endpointHom,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.contractionHom,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraPathFunctor,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat_hom,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat_hom,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.prepathAlgebra,
      `SerrePositivity.EInfinity.projectiveCofibration_degreewise_isSplitMono,
      `SerrePositivity.EInfinity.homPrecompose_degreewise_surjective,
      `SerrePositivity.EInfinity.homPrecompose_projectiveFibration,
      `SerrePositivity.EInfinity.homBiprodRestriction,
      `SerrePositivity.EInfinity.homBiprodRestriction_degreewise_surjective,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationPair_eq_boundary,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationPair_projectiveFibration,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationPair_projectiveFibration,
      `SerrePositivity.EInfinity.projectiveCofibrant_sphere,
      `SerrePositivity.EInfinity.projectiveCofibrant_unit,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.endpoint_false_cofibration,
      `SerrePositivity.EInfinity.projectiveTrivialCofibration_llp,
      `SerrePositivity.EInfinity.projectiveTrivialCofibration_homotopyEquiv,
      `SerrePositivity.EInfinity.homPrecomposeHomotopy,
      `SerrePositivity.EInfinity.homPrecomposeHomotopyEquiv,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.constant_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluation_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat_quasiIso,
      `SerrePositivity.EInfinity.tensorInsertionBlock_naturality,
      `SerrePositivity.EInfinity.tensorInsertionAction_base_naturality,
      `SerrePositivity.EInfinity.Operad.Algebra.ofJointlyMonicActions,
      `SerrePositivity.EInfinity.Operad.Algebra.binaryProduct,
      `SerrePositivity.EInfinity.Operad.Algebra.binaryProductIsLimit,
      `SerrePositivity.EInfinity.Operad.Algebra.binaryProductIso,
      `SerrePositivity.EInfinity.Operad.Algebra.terminalAlgebraIsTerminal,
      `SerrePositivity.EInfinity.Operad.Algebra.weakEquivalenceStructure,
      `SerrePositivity.EInfinity.Operad.Algebra.fibrationStructure,
      `SerrePositivity.EInfinity.Operad.Algebra.toTerminal_projectiveFibration,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.prepathAlgebra_p_compare,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.pathAlgebra,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.pathAlgebra_isGood,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.exists_retraction_path,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.fibrations_llp_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_rlp,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_llp_le,
      Name.str `SerrePositivity.EInfinity.Operad.CoalgebraInterval
        "freeGeneratingTrivialCofibrations_cell_acyclicity",
      `SerrePositivity.EInfinity.Operad.Algebra.forget_reflectsIsomorphisms,
      `SerrePositivity.EInfinity.Operad.Algebra.ofLimitCone,
      `SerrePositivity.EInfinity.Operad.Algebra.algebraLimitIsLimit,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_createsLimit,
      `SerrePositivity.EInfinity.tensorPower_preservesSiftedColimits_of_tensor,
      `SerrePositivity.EInfinity.tensorPower_preservesSiftedColimits,
      `SerrePositivity.EInfinity.schurFunctor_preservesSiftedColimits,
      `SerrePositivity.EInfinity.schurFunctor_preservesFilteredColimits,
      `SerrePositivity.EInfinity.Operad.freeAlgebraForget_preservesSiftedColimits,
      `SerrePositivity.EInfinity.Operad.freeAlgebraForget_preservesFilteredColimits,
      `SerrePositivity.EInfinity.Operad.Algebra.ofJointlyEpicActions,
      `SerrePositivity.EInfinity.Operad.Algebra.ofColimitCocone,
      `SerrePositivity.EInfinity.Operad.Algebra.algebraColimitIsColimit,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_createsColimit,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_createsSiftedColimitsOfShape,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_createsFilteredColimitsOfShape,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_monadic,
      `SerrePositivity.EInfinity.walkingReflexivePair_isSifted,
      `SerrePositivity.EInfinity.Operad.Algebra.hasReflexiveCoequalizers,
      `SerrePositivity.EInfinity.Operad.Algebra.diagramForget_monadic,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_isCardinalAccessible,
      `SerrePositivity.EInfinity.Operad.freeAlgebra_finitelyPresentable,
      `SerrePositivity.EInfinity.Operad.freeGeneratingCofibrations_smallObjectArgument,
      `SerrePositivity.EInfinity.Operad.freeGeneratingTrivialCofibrations_smallObjectArgument,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory_weakEquivalences,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory_fibrations,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory_cofibrantlyGenerated,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory_forget_isRightQuillen,
      `SerrePositivity.EInfinity.Surjection.BasisWord,
      `SerrePositivity.EInfinity.Surjection.degreeZeroEquiv,
      `SerrePositivity.EInfinity.Surjection.barrattEcclesWord_action,
      `SerrePositivity.EInfinity.Surjection.card_caesuras_basisWord,
      `SerrePositivity.EInfinity.Surjection.deletionCoefficient_final,
      `SerrePositivity.EInfinity.Surjection.representation,
      `SerrePositivity.EInfinity.Surjection.differential_basis,
      `SerrePositivity.EInfinity.Surjection.differential_renameLinear,
      `SerrePositivity.EInfinity.Surjection.listGenerator_ofFn,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_length,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_map,
      `SerrePositivity.EInfinity.TableReduction.output_length,
      `SerrePositivity.EInfinity.TableReduction.onSequence_action,
      `SerrePositivity.EInfinity.TableReduction.onSequence_degree_zero,
      `SerrePositivity.EInfinity.TableReduction.onSequence_nullary_zero,
      `SerrePositivity.EInfinity.TableReduction.onSequence_nullary_succ,
      `SerrePositivity.EInfinity.TableReduction.degreeMap_basis,
      `SerrePositivity.EInfinity.TableReduction.available_after_take,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_same_adjacent_not_isChain,
      `SerrePositivity.EInfinity.Surjection.listGenerator_eq_zero_of_not_isChain,
      `SerrePositivity.EInfinity.TableReduction.output_not_isChain_of_adjacent_eq,
      `SerrePositivity.EInfinity.TableReduction.onSequence_eq_zero_of_adjacent_eq,
      `SerrePositivity.EInfinity.TableReduction.onSequence_eq_zero_of_degenerate,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_generator,
      `SerrePositivity.EInfinity.TableReduction.degreeMap_action,
      `SerrePositivity.EInfinity.Surjection.firstOccurrences_nodup,
      `SerrePositivity.EInfinity.Surjection.caesuraList_eq_sort,
      `SerrePositivity.EInfinity.Surjection.rowStart_strictMono,
      `SerrePositivity.EInfinity.Surjection.rowStart_lt_length,
      `SerrePositivity.EInfinity.TableReduction.canonicalRow_nodup,
      `SerrePositivity.EInfinity.TableReduction.canonicalRow_word_length,
      `SerrePositivity.EInfinity.TableReduction.canonicalPermutation_inv_list,
      `SerrePositivity.EInfinity.TableReduction.canonicalSimplex,
      `SerrePositivity.EInfinity.TableReduction.rows_canonicalVertices,
      `SerrePositivity.EInfinity.Surjection.firstOccurrences_cons,
      `SerrePositivity.EInfinity.Surjection.caesura_iff_mem_drop,
      `SerrePositivity.EInfinity.TableReduction.canonicalRow_succ_of_not_mem,
      `SerrePositivity.EInfinity.TableReduction.canonicalRow_exists_move,
      `SerrePositivity.EInfinity.TableReduction.canonicalRow_eq_of_final_interval,
      `SerrePositivity.EInfinity.Surjection.not_caesura_between_start_and_cut,
      `SerrePositivity.EInfinity.TableReduction.canonicalRows_adjacent_exists_move,
      `SerrePositivity.EInfinity.TableReduction.canonicalVertices_ne_adjacent,
      `SerrePositivity.EInfinity.TableReduction.canonicalSimplex_mem_nonDegenerate,
      `SerrePositivity.EInfinity.TableReduction.canonicalNondegenerateSimplex,
      `SerrePositivity.EInfinity.TableReduction.available_moved_wrong_cut_head,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_forces_move_length,
      `SerrePositivity.EInfinity.TableReduction.pastFinals_eq_append_segment,
      `SerrePositivity.EInfinity.TableReduction.canonicalRows_force_length,
      `SerrePositivity.EInfinity.TableReduction.canonicalRows_extract_original_segment,
      `SerrePositivity.EInfinity.TableReduction.canonicalRows_exclusion_update,
      `SerrePositivity.EInfinity.Surjection.not_caesura_after_last_start,
      `SerrePositivity.EInfinity.TableReduction.available_canonicalRow_last,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_canonical_last,
      `SerrePositivity.EInfinity.TableReduction.canonicalLengths_sum,
      `SerrePositivity.EInfinity.TableReduction.canonicalSchedule,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_canonical,
      `SerrePositivity.EInfinity.TableReduction.schedule_eq_canonical_of_isChain,
      `SerrePositivity.EInfinity.TableReduction.onSequence_canonical,
      `SerrePositivity.EInfinity.TableReduction.degreeMap_comp_section,
      `SerrePositivity.EInfinity.TableReduction.degreeMap_surjective,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_surjective,
      `SerrePositivity.EInfinity.Surjection.deletionCoefficient_adjacent_eq,
      `SerrePositivity.EInfinity.Surjection.erase_adjacent_eq,
      `SerrePositivity.EInfinity.Surjection.rawDifferential_eq_zero_of_not_nondegenerate,
      `SerrePositivity.EInfinity.Surjection.differential_generator,
      `SerrePositivity.EInfinity.Surjection.differential_listGenerator,
      `SerrePositivity.EInfinity.TableReduction.differential_onSequence,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_d_generator,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_comm_iff_vertexBoundary,
      `SerrePositivity.EInfinity.TableReduction.differential_onSequence_nullary,
      `SerrePositivity.EInfinity.TableReduction.transferUnit_inverse,
      `SerrePositivity.EInfinity.TableReduction.scheduleTransfer,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_delete_singleton,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace,
      `SerrePositivity.EInfinity.TableReduction.extractionTrace_of_reduceRows,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.removed_not_mem_output,
      `SerrePositivity.EInfinity.TableReduction.separatedRows_of_reduction,
      `SerrePositivity.EInfinity.Surjection.card_caesuras_ge,
      `SerrePositivity.EInfinity.TableReduction.recurrentEnds_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.rowEnds_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.rowEnds_caesura_iff,
      `SerrePositivity.EInfinity.Surjection.caesuraRank_caesuraAt,
      `SerrePositivity.EInfinity.TableReduction.rowEndSigns_of_reduction,
      `SerrePositivity.EInfinity.Surjection.caesuraRank_raw_get,
      `SerrePositivity.EInfinity.Surjection.deletionCoefficient_raw_get,
      `SerrePositivity.EInfinity.TableReduction.rawRowEndSigns_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.rowEndOffsets_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.singletonScheduleEquiv,
      `SerrePositivity.EInfinity.TableReduction.rows_scheduleDelete,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_deleted_vertex,
      `SerrePositivity.EInfinity.TableReduction.deletionCoefficient_schedule_rowEnd,
      `SerrePositivity.EInfinity.TableReduction.deletionCoefficient_singleton_final,
      `SerrePositivity.EInfinity.TableReduction.deletionCoefficient_singleton,
      `SerrePositivity.EInfinity.TableReduction.singleton_boundary_certificate,
      `SerrePositivity.EInfinity.TableReduction.rows_prefix_budget,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_inserted_vertex,
      `SerrePositivity.EInfinity.TableReduction.singleton_reduction_none_iff,
      `SerrePositivity.EInfinity.TableReduction.singleton_deletion_term,
      `SerrePositivity.EInfinity.TableReduction.sum_singletonSchedules_vertexBoundary,
      `SerrePositivity.EInfinity.Surjection.listDeletionTerm,
      `SerrePositivity.EInfinity.Surjection.rawListDifferential_eq_sum,
      `SerrePositivity.EInfinity.TableReduction.scheduleOffset_strictMono,
      `SerrePositivity.EInfinity.TableReduction.outputPosition_injective,
      `SerrePositivity.EInfinity.TableReduction.singletonPositions,
      `SerrePositivity.EInfinity.TableReduction.sum_singletonPositions,
      `SerrePositivity.EInfinity.TableReduction.rawListDifferential_partition,
      `SerrePositivity.EInfinity.TableReduction.remainderTerm,
      `SerrePositivity.EInfinity.TableReduction.differential_term_partition,
      `SerrePositivity.EInfinity.TableReduction.sum_singleton_terms_vertexBoundary,
      `SerrePositivity.EInfinity.TableReduction.differential_onSequence_vertexBoundary_add_remainder,
      `SerrePositivity.EInfinity.TableReduction.vertexBoundary_identity_iff_remainder_zero,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_comm_iff_remainder_zero,
      `SerrePositivity.EInfinity.TableReduction.schedule_excess_sum,
      `SerrePositivity.EInfinity.TableReduction.schedule_receiver_lt,
      `SerrePositivity.EInfinity.TableReduction.deletionScheduleTransfer,
      `SerrePositivity.EInfinity.TableReduction.deletionScheduleTransfer_inverse,
      `SerrePositivity.EInfinity.TableReduction.flatten_position_decomposition,
      `SerrePositivity.EInfinity.TableReduction.previous_position_lt_row_start,
      `SerrePositivity.EInfinity.TableReduction.row_lt_of_end_lt_start,
      `SerrePositivity.EInfinity.TableReduction.previousOccurrence_scheduleEnd,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_coefficient_receiver,
      `SerrePositivity.EInfinity.TableReduction.output_position_owner,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_rows,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_congr_removed,
      `SerrePositivity.EInfinity.TableReduction.donor_selected_split,
      `SerrePositivity.EInfinity.TableReduction.donor_exclusion_equiv,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_donor_step,
      `SerrePositivity.EInfinity.TableReduction.intermediate_selected_eq,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix,
      `SerrePositivity.EInfinity.TableReduction.extractionPrefix_of_reduceRows,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.early_exclusion,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.append_early_exclusion,
      `SerrePositivity.EInfinity.TableReduction.receiver_capacity_of_tail,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_receiver_step,
      `SerrePositivity.EInfinity.TableReduction.transfer_block_extraction,
      `SerrePositivity.EInfinity.TableReduction.transfer_block_deleted_outputs,
      `SerrePositivity.EInfinity.Surjection.previousOccurrence_no_between,
      `SerrePositivity.EInfinity.Surjection.previousOccurrence_not_mem_slice,
      `SerrePositivity.EInfinity.TableReduction.rows_deletionScheduleTransfer,
      `SerrePositivity.EInfinity.TableReduction.ofFn_split_two,
      `SerrePositivity.EInfinity.TableReduction.rows_transfer_blocks,
      `SerrePositivity.EInfinity.TableReduction.two_row_extraction,
      `SerrePositivity.EInfinity.TableReduction.rows_prefix_sum,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_location,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_row_cases,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_terminal_donor_step,
      `SerrePositivity.EInfinity.TableReduction.terminal_transfer_block_deleted_outputs,
      `SerrePositivity.EInfinity.TableReduction.scheduleBlock_nonempty,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.receiver_end_value,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.donor_value,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.previousOccurrence_not_mem_middle,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.donor_split,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.receiver_capacity,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.lift_transfer,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_transfer,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_pair,
      `SerrePositivity.EInfinity.TableReduction.scheduleEnd_not_singleton,
      `SerrePositivity.EInfinity.TableReduction.residual_caesura_row,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_released_donor_step,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.finish_length,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.finish_nodup,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.trans,
      `SerrePositivity.EInfinity.TableReduction.available_vertexRow_length_add,
      `SerrePositivity.EInfinity.TableReduction.available_vertexRow_release_length,
      `SerrePositivity.EInfinity.TableReduction.released_value_mem_extended_take,
      `SerrePositivity.EInfinity.TableReduction.before_last_excess,
      `SerrePositivity.EInfinity.TableReduction.last_row_available_length,
      `SerrePositivity.EInfinity.TableReduction.final_prefix_saturated,
      `SerrePositivity.EInfinity.TableReduction.CompleteRows,
      `SerrePositivity.EInfinity.TableReduction.completeRows_rows,
      `SerrePositivity.EInfinity.TableReduction.released_state_step,
      `SerrePositivity.EInfinity.TableReduction.ReleaseSearch,
      `SerrePositivity.EInfinity.TableReduction.releaseSearch_exists,
      `SerrePositivity.EInfinity.TableReduction.ReleaseSearch.toPrefix,
      `SerrePositivity.EInfinity.TableReduction.ReleaseSearch.unique,
      `SerrePositivity.EInfinity.TableReduction.released_suffix_budget,
      `SerrePositivity.EInfinity.TableReduction.releaseSearch_on_schedule_suffix,
      `SerrePositivity.EInfinity.TableReduction.releaseSearch_constructs_extension,
      `SerrePositivity.EInfinity.TableReduction.receiver_release,
      `SerrePositivity.EInfinity.TableReduction.reverse_block_extraction,
      `SerrePositivity.EInfinity.TableReduction.nonfinalRowPrefix_nonempty,
      `SerrePositivity.EInfinity.TableReduction.reverseTransferData_nonempty,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.split_success,
      `SerrePositivity.EInfinity.TableReduction.previousOccurrence_double_insert,
      `SerrePositivity.EInfinity.TableReduction.position_in_long_row_not_singleton,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.shortened_end,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_not_caesura,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_previousOccurrence,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_coefficient,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.pair_cancel,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_in_late_row,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_not_singleton,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.forward_rows,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.forward_schedule,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.forward_position,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.unique,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.prepend_releaseSearch,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.forward_release_search,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.reverse_search,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.reverse_result,
      `SerrePositivity.EInfinity.TableReduction.DeletionPoint,
      `SerrePositivity.EInfinity.TableReduction.deletionEquiv,
      `SerrePositivity.EInfinity.TableReduction.backward_forwardDeletion,
      `SerrePositivity.EInfinity.TableReduction.forward_backwardDeletion,
      `SerrePositivity.EInfinity.TableReduction.sum_remainingValue_zero,
      `SerrePositivity.EInfinity.TableReduction.sum_remainderTerm_eq_points,
      `SerrePositivity.EInfinity.TableReduction.sum_remainderTerm_zero,
      `SerrePositivity.EInfinity.TableReduction.differential_onSequence_eq_vertexBoundary,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_comm,
      `SerrePositivity.EInfinity.TableReduction.differential_comp_differential,
      `SerrePositivity.EInfinity.Surjection.normalizedChains,
      `SerrePositivity.EInfinity.TableReduction.chainMap,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.start_add_length_le,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.position_covered,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.value_mem_segments,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_strictMono,
      `SerrePositivity.EInfinity.Surjection.substitute_length,
      `SerrePositivity.EInfinity.Surjection.compositeWord_length,
      `SerrePositivity.EInfinity.Surjection.compositeWord_surjective,
      `SerrePositivity.EInfinity.Surjection.compositionExponent,
      `SerrePositivity.EInfinity.Surjection.compositionSign,
      `SerrePositivity.EInfinity.Surjection.compositionOnWords,
      `SerrePositivity.EInfinity.Surjection.partialComposition,
      `SerrePositivity.EInfinity.Surjection.partialComposition_basis,
      `SerrePositivity.EInfinity.Surjection.compositionOnWords_nullary_of_count_ne_one,
      `SerrePositivity.EInfinity.Surjection.substitute_isChain,
      `SerrePositivity.EInfinity.Surjection.compositeWord_nondegenerate,
      `SerrePositivity.EInfinity.Surjection.compositeBasisWord,
      `SerrePositivity.EInfinity.Surjection.compositeGenerator_eq_basis,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.boundary_mono,
      `SerrePositivity.EInfinity.Surjection.lineRank_last,
      `SerrePositivity.EInfinity.Surjection.sum_segmentDegree,
      `SerrePositivity.EInfinity.Surjection.sum_outerSegmentDegree,
      `SerrePositivity.EInfinity.Surjection.sum_outerSegmentDegree_suffix,
      `SerrePositivity.EInfinity.Surjection.compositionExponent_eq_component_exchanges,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_sign,
      `SerrePositivity.EInfinity.Surjection.DegreePath.blocks_sign,
      `SerrePositivity.EInfinity.Surjection.compositionPath,
      `SerrePositivity.EInfinity.Surjection.compositionPath_blockExponent,
      `SerrePositivity.EInfinity.Surjection.compositionPath_sign,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_inverse_row,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_inverse_row_substitute,
      `SerrePositivity.EInfinity.Surjection.remaining_mem_compositionRemoved,
      `SerrePositivity.EInfinity.Surjection.inserted_mem_compositionRemoved,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_available_substitute,
      `SerrePositivity.EInfinity.Surjection.compositionStateRemoved,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_state_available_substitute,
      `SerrePositivity.EInfinity.Surjection.compositionStateRemoved_update,
      `SerrePositivity.EInfinity.Surjection.compositionStateRemoved_finalize,
      `SerrePositivity.EInfinity.Surjection.compositionSelectedUpdate_before,
      `SerrePositivity.EInfinity.Surjection.compositionSelectedUpdate_inside,
      `SerrePositivity.EInfinity.Surjection.compositionSelectedUpdate_after,
      `SerrePositivity.EInfinity.Surjection.compositionExtractionStep_before,
      `SerrePositivity.EInfinity.Surjection.compositionExtractionStep_inside,
      `SerrePositivity.EInfinity.Surjection.compositionExtractionStep_after,
      `SerrePositivity.EInfinity.Surjection.lineRank_eq_rawCaesura_count,
      `SerrePositivity.EInfinity.TableReduction.rowEndPositions_count_before_in_row,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.lineRank_in_row,
      `SerrePositivity.EInfinity.TableReduction.lineRank_schedule_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.reductionRow,
      `SerrePositivity.EInfinity.TableReduction.reductionRow_bounds,
      `SerrePositivity.EInfinity.TableReduction.reductionRow_eq_iff,
      `SerrePositivity.EInfinity.TableReduction.reductionRow_mono,
      `SerrePositivity.EInfinity.Surjection.segmentDegree_eq_reductionRows,
      `SerrePositivity.EInfinity.Surjection.outerSegmentDegree_eq_reductionRows,
      `SerrePositivity.EInfinity.TableReduction.reductionRow_lt_of_repeat,
      `SerrePositivity.EInfinity.TableReduction.occurrence_reductionRow_strictMono,
      `SerrePositivity.EInfinity.TableReduction.scheduleRowCursor_nonempty,
      `SerrePositivity.EInfinity.TableReduction.reductionColumn_position,
      `SerrePositivity.EInfinity.TableReduction.ScheduleRowCursor.reductionColumn_value,
      `SerrePositivity.EInfinity.TableReduction.ScheduleRowCursor.available_slot_split,
      `SerrePositivity.EInfinity.TableReduction.reductionCursor_composite_row,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.unique,
      `SerrePositivity.EInfinity.TableReduction.ScheduleRowCursor.next_state,
      `SerrePositivity.EInfinity.TableReduction.ScheduleRowCursor.remainder_success_eq_drop,
      `SerrePositivity.EInfinity.TableReduction.rowInterval_prefix,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.interval_prefix_word,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.interval_source_rows,
      `SerrePositivity.EInfinity.TableReduction.cursorInterval_nonempty,
      `SerrePositivity.EInfinity.TableReduction.reductionInterval_nonempty,
      `SerrePositivity.EInfinity.TableReduction.ReductionInterval.success,
      `SerrePositivity.EInfinity.Surjection.componentExtraction_word,
      `SerrePositivity.EInfinity.Surjection.componentExtraction_length,
      `SerrePositivity.EInfinity.Surjection.componentExtraction_success,
      `SerrePositivity.EInfinity.Surjection.componentExtraction_adjacent_prefix,
      `SerrePositivity.EInfinity.Surjection.outerComponentExtraction_success,
      `SerrePositivity.EInfinity.Surjection.verticalExtraction_success,
      `SerrePositivity.EInfinity.TableReduction.ReductionInterval.permutationRows_eq,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_available_slot,
      `SerrePositivity.EInfinity.Surjection.componentVerticalExtraction_success,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_removed_eq,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_word_eq,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_of_success,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.not_mem_initial,
      `SerrePositivity.EInfinity.Surjection.substitute_head_prefix,
      `SerrePositivity.EInfinity.Surjection.horizontalLabel_state_update,
      `SerrePositivity.EInfinity.Surjection.horizontalExtractionStep_success,
      `SerrePositivity.EInfinity.Surjection.horizontalExtraction_success,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_available_head,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_not_mem,
      `SerrePositivity.EInfinity.Surjection.componentHorizontalExtraction_success,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_last_singleton,
      `SerrePositivity.EInfinity.Surjection.horizontalLabel_injective,
      `SerrePositivity.EInfinity.Surjection.substitute_singleton_nodup,
      `SerrePositivity.EInfinity.Surjection.horizontalLabel_singleton_state_update,
      `SerrePositivity.EInfinity.Surjection.singletonHorizontalExtraction_success,
      `SerrePositivity.EInfinity.Surjection.finalHorizontalExtraction_success,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.raw_success_zero,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fused_success_zero,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedWord_step,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fused_success_blockWord,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedWord_eq_blockWord,
      `SerrePositivity.EInfinity.Surjection.substitute_append,
      `SerrePositivity.EInfinity.Surjection.substitute_at_occurrence,
      `SerrePositivity.EInfinity.Surjection.compositeWord_at_occurrence,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.firstHorizontal_dropLast,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.middleHorizontal_dropLast,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.finalHorizontal_word,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.verticalWord_append_endpoint,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.blockWord_eq_compositeWord,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fused_success_compositeWord,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedRows_length,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedSchedule,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.rows_fusedSchedule_of_fst,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.horizontalRows_fst,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.verticalRows_fst,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedRows_fst_step,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_horizontal_front,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_horizontal_back,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_vertical_front,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_vertical_back,
      `SerrePositivity.EInfinity.Surjection.DegreePath.vertices_append,
      `SerrePositivity.EInfinity.Surjection.DegreePath.vertices_blocks,
      `SerrePositivity.EInfinity.Surjection.compositionPath_vertices,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.rowAtGrid_valid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.horizontalRows_eq_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.verticalRows_eq_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedRows_eq_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.pathSequence_rows_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.pathSequence_success_of_vertices,
      `SerrePositivity.EInfinity.Surjection.DegreePath.walkVertices_eq_blocks,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.compositionPath_vertices_eq_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.rows_pathSequence,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.pathSequence_success,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.term_shuffleSimplex,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.signed_term_shuffleSimplex,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerWord_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.inner_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerWord_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.input_words_unique,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.splitParts_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.partition_unique,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.partsOfWord_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.composite_data_injective,
      `SerrePositivity.EInfinity.TableReduction.schedule_eq_of_same_output,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_reordered_endpoint_not_isChain,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_block_endpoint_mem_middle,
      `SerrePositivity.EInfinity.TableReduction.available_block_next_head_mem_middle,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_vertical_endpoint_inserted,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_vertical_next_head_inserted,
      `SerrePositivity.EInfinity.TableReduction.available_filterMap,
      `SerrePositivity.EInfinity.TableReduction.filterMap_selection_retained_last,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.filterMap,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerLabel_available_composition_row,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_vertical_inner_step,
      `SerrePositivity.EInfinity.Surjection.vertical_prefix_inner_projection,
      `SerrePositivity.EInfinity.Surjection.vertical_prefix_inner_rows,
      `SerrePositivity.EInfinity.TableReduction.filterMap_selection_discarded_last,
      `SerrePositivity.EInfinity.TableReduction.filterMap_final_prefix,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_vertical_inner_pair,
      `SerrePositivity.EInfinity.Surjection.vertical_interval_final_inner_nonempty,
      `SerrePositivity.EInfinity.Surjection.vertical_interval_inner_projection,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recovered_state_mem,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recovered_available_substitute,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerRemoved_nil,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerRemoved_subset,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerLabel_available_composition_row,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_take_prefix,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_drop_rank,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_take,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_bounds,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_update_mem,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_step,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outer_table_success,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_collapse,
      `SerrePositivity.EInfinity.TableReduction.compressRows_fst,
      `SerrePositivity.EInfinity.TableReduction.compressRows_success,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_flatten,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.compressed_outer_table_success,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_boundary_ne,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_horizontal_inner_boundary_eq,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_horizontal_outer_boundary_ne,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_nodup,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.horizontal_outer_selections_isChain,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_isChain_of_tail,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.compress_isChain,
      `SerrePositivity.EInfinity.TableReduction.extractionTrace_of_lengths,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recoveredOuterTable_trace,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recoveredOuterTable_separated,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.compressed_outer_table_nondegenerate,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_ofFn_orderHom,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffleTableEntries_axis,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_recovery,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_compressed_outer_rows,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_isChain_of_success,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_inner_isChain_of_success,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_recovery_with_rows,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffleSimplex_outer_recovery,
      `SerrePositivity.EInfinity.TableReduction.output_covers,
      `SerrePositivity.EInfinity.TableReduction.schedule_of_table,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_excess,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_schedule,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_basis,
      `SerrePositivity.EInfinity.TableReduction.ConsumptionPrefix.normalize,
      `SerrePositivity.EInfinity.TableReduction.ConsumptionPrefix.close_of_prefix,
      `SerrePositivity.EInfinity.TableReduction.ConsumptionPrefix.reduction,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.filterMap_consumption,
      `SerrePositivity.EInfinity.Surjection.horizontal_inner_consumption,
      `SerrePositivity.EInfinity.Surjection.horizontal_inner_close,
      `SerrePositivity.EInfinity.Surjection.horizontal_inner_before_vertical,
      `SerrePositivity.EInfinity.Surjection.horizontal_inner_success,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_isChain,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_append_of_separated,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerWord_append_of_retained,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerRunDecomposition_exists,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.InnerRunDecomposition.sources_eq,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.vertical_inner_join,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.inner_table_success,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerWord_covers,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_inner_recovery_with_rows,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.recurrent_tail,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.recurrent_of_schedule,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.InnerRunDecomposition.inner_recurrent,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.inner_recurrent_table_success,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_inner_schedule,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_inner_basis,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_append_length,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.shared_endpoints_of_saturated,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.shared_rows_take,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.ofRows,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.ofRows_segments,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.existsUnique_of_rows,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerWord_remaining_cons,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.exists_nonempty_parts,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.splitParts_properties,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recovered_partition_existsUnique,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_source_partition,
      `SerrePositivity.EInfinity.TableReduction.schedule_eq_of_same_list,
      `SerrePositivity.EInfinity.TableReduction.selected_eq_of_same_output,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.vertical_inserted_join,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.horizontal_not_inserted_join,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.boundaryInserted_iff_notMem,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shufflePath_eq_of_same_output,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.compositionPath_eq_of_success,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedSchedule_eq_of_success,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.eq_of_same_output,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_reconstruction_existsUnique,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.equiv,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.sourceFintype,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.forward_term,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.signedTerm_eq_zero_of_not_successful,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.sum_all_eq_source,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.sum_onSequence_eq_source,
      `SerrePositivity.EInfinity.TableReduction.word_exists_of_success,
      `SerrePositivity.EInfinity.TableReduction.term_eq_sum_words,
      `SerrePositivity.EInfinity.TableReduction.onSequence_eq_sum_successfulWords,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.wordsEquiv,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.sum_source_eq_partialComposition,
      `SerrePositivity.EInfinity.TableReduction.onSequence_partialComposition_of_pos,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffle_generators_of_pos,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffleBilinear_of_pos,
      `SerrePositivity.EInfinity.TableReduction.onSequence_shuffle_nullary_succ,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffleBilinear_nullary_succ,
      `SerrePositivity.EInfinity.Surjection.substitute_nullary,
      `SerrePositivity.EInfinity.Surjection.eraseSlotLabel_partial_injective,
      `SerrePositivity.EInfinity.Surjection.eraseSlotWord_length,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_inverse_row_nullary,
      `SerrePositivity.EInfinity.Surjection.compositionOnWords_nullary_of_count_eq_one,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_filterMap_of_discarded_mem,
      `SerrePositivity.EInfinity.TableReduction.permutationComposition_nullary_available,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_eraseSlotWord_of_mem,
      `SerrePositivity.EInfinity.TableReduction.rows_nullary,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_nullary,
      `SerrePositivity.EInfinity.TableReduction.completeRows_nullarySourceRows,
      `SerrePositivity.EInfinity.TableReduction.nullary_success_extension,
      `SerrePositivity.EInfinity.TableReduction.nullary_success_schedule,
      `SerrePositivity.EInfinity.Surjection.isChain_insert_of_eraseSlotWord,
      `SerrePositivity.EInfinity.TableReduction.nullary_successfulWord_lift_exists,
      `SerrePositivity.EInfinity.TableReduction.nullary_successfulWord_lift_term,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.filterMap_reduceRows,
      `SerrePositivity.EInfinity.TableReduction.recurrentEnds_eraseSlotWord_ready,
      `SerrePositivity.EInfinity.TableReduction.nullary_forward_schedule,
      `SerrePositivity.EInfinity.TableReduction.nullary_successfulWord_forward_exists,
      `SerrePositivity.EInfinity.TableReduction.nullarySourceFintype,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward_word,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward_surjective,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward_term,
      `SerrePositivity.EInfinity.TableReduction.take_length_eq_of_filterMap_eq,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.eq_of_filterMap,
      `SerrePositivity.EInfinity.TableReduction.nullary_projected_selected_eq,
      `SerrePositivity.EInfinity.TableReduction.nullary_success_output_unique,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward_injective,
      `SerrePositivity.EInfinity.TableReduction.nullarySuccessEquiv,
      `SerrePositivity.EInfinity.TableReduction.sum_nullary_source_eq_target,
      `SerrePositivity.EInfinity.TableReduction.sum_nullary_all_eq_source,
      `SerrePositivity.EInfinity.TableReduction.onSequence_partialComposition_nullary_zero,
      `SerrePositivity.EInfinity.TableReduction.onSequence_partialComposition,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffle_generators,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffleBilinear,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_degreeTransport,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_arityTransport,
      `SerrePositivity.EInfinity.Surjection.partialComposition_d_positive,
      `SerrePositivity.EInfinity.Surjection.partialComposition_d_leftZero,
      `SerrePositivity.EInfinity.Surjection.partialComposition_d_rightZero,
      `SerrePositivity.EInfinity.Surjection.unitElement,
      `SerrePositivity.EInfinity.Surjection.partialComposition_left_unit,
      `SerrePositivity.EInfinity.Surjection.partialComposition_right_unit,
      `SerrePositivity.EInfinity.Surjection.partialComposition_nested_assoc,
      `SerrePositivity.EInfinity.Surjection.partialComposition_parallel_assoc,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_rightAction,
      `SerrePositivity.EInfinity.Surjection.partialComposition_inner_rightAction,
      `SerrePositivity.EInfinity.Surjection.partialComposition_outer_rightAction,
      `SerrePositivity.EInfinity.Surjection.complex,
      `SerrePositivity.EInfinity.Surjection.complexXIso,
      `SerrePositivity.EInfinity.Surjection.complex_isZero_positive,
      `SerrePositivity.EInfinity.Surjection.normalizedRename,
      `SerrePositivity.EInfinity.Surjection.complexRename,
      `SerrePositivity.EInfinity.Surjection.sequence,
      `SerrePositivity.EInfinity.TableReduction.cochainMap,
      `SerrePositivity.EInfinity.TableReduction.cochainMap_f_surjective,
      `SerrePositivity.EInfinity.TableReduction.sequenceMap,
      `SerrePositivity.EInfinity.Surjection.cochainCompositionBilinear,
      `SerrePositivity.EInfinity.TableReduction.cochainMap_f_surjective_int,
      `SerrePositivity.EInfinity.TableReduction.cochainMap_compositionBilinear,
      `SerrePositivity.EInfinity.Surjection.cochainCompositionBilinear_d,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition,
      `SerrePositivity.EInfinity.Surjection.ι_complexPartialComposition,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_neg_tmul,
      `SerrePositivity.EInfinity.TableReduction.complexPartialComposition_comm,
      `SerrePositivity.EInfinity.Surjection.complexUnit,
      `SerrePositivity.EInfinity.Surjection.complexUnit_comm,
      `SerrePositivity.EInfinity.Surjection.complexUnit_zero_apply,
      `SerrePositivity.EInfinity.TableReduction.cochainMap_epi,
      `SerrePositivity.EInfinity.TableReduction.tensor_epi_of_epi,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_left_unit,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_right_unit,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_inner_rightAction,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_outer_rightAction,
      `SerrePositivity.EInfinity.TableReduction.triple_cochainMap_epi,
      `SerrePositivity.EInfinity.TableReduction.exchangeLastFactors_naturality,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_nested_assoc,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_parallel_assoc,
      `SerrePositivity.EInfinity.Surjection.operad,
      `SerrePositivity.EInfinity.TableReduction.operadMap,
      `SerrePositivity.EInfinity.TableReduction.operadMap_app,
      `SerrePositivity.EInfinity.TableReduction.operadMap_f_surjective,
      `SerrePositivity.EInfinity.IntervalCuts.edge_degree_bound,
      `SerrePositivity.EInfinity.IntervalCuts.vertexNondegenerate_iff,
      `SerrePositivity.EInfinity.IntervalCuts.sum_edgeOutputDegree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign,
      `SerrePositivity.EInfinity.IntervalCuts.edgeValue,
      `SerrePositivity.EInfinity.IntervalCuts.vertexValue,
      `SerrePositivity.EInfinity.IntervalCuts.edgeLinear,
      `SerrePositivity.EInfinity.IntervalCuts.vertexLinear,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_total_degree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeValue_eq_zero_of_degree,
      `SerrePositivity.EInfinity.IntervalCuts.interval,
      `SerrePositivity.EInfinity.IntervalCuts.intervalXIso,
      `SerrePositivity.EInfinity.IntervalCuts.faceChain,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector,
      `SerrePositivity.EInfinity.IntervalCuts.edgeChain_d,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVector,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorOfDegree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_tupleDegree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_basis,
      `SerrePositivity.EInfinity.IntervalCuts.intervalChains_isZero,
      `SerrePositivity.EInfinity.IntervalCuts.interval_isZero_positive,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector_edge_d,
      `SerrePositivity.EInfinity.IntervalCuts.tensorPair_d_apply,
      `SerrePositivity.EInfinity.IntervalCuts.tensorBoundaryTerm,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVector_d,
      `SerrePositivity.EInfinity.IntervalCuts.simplex_cases,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector_vertex_d,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector_edge_d_sub,
      `SerrePositivity.EInfinity.IntervalCuts.tensorBoundaryTerm_eq_zero_of_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVector_d_eq_zero_of_vertices,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVector_d_eq_sum_edges,
      `SerrePositivity.EInfinity.IntervalCuts.tensorBoundaryTerm_zero_edge,
      `SerrePositivity.EInfinity.IntervalCuts.edgeNondegenerate_iff,
      `SerrePositivity.EInfinity.IntervalCuts.repeated_straddles,
      `SerrePositivity.EInfinity.IntervalCuts.caesura_before_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.edgePositionExponent_eq_zero,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_of_nondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.activePositions,
      `SerrePositivity.EInfinity.IntervalCuts.activePositions_card,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_eq_edge_iff,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_tensorVector_d,
      `SerrePositivity.EInfinity.IntervalCuts.erase_edgeNondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.eraseCutBasisWord,
      `SerrePositivity.EInfinity.IntervalCuts.generator_erase_of_cut,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutputVertices_erase_of_ne,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_eraseCut_left,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_eraseCut_right,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount,
      `SerrePositivity.EInfinity.IntervalCuts.edgePermutationExponent_eq_inversionCount,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_eq_inversionCount,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_erase_balance,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionSign_erase,
      `SerrePositivity.EInfinity.IntervalCuts.positionRank_active_caesura,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_prefix_degree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_caesura_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.deletionCoefficient_repeat_pair,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_final_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.caesura_erase_iff_of_cut,
      `SerrePositivity.EInfinity.IntervalCuts.activePositions_erase_image_eq_erase,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_image,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_erase_eq_removed,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_erase_left_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_erase_right_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt_succ,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt_natDegree,
      `SerrePositivity.EInfinity.IntervalCuts.tupleDegree_update_edge,
      `SerrePositivity.EInfinity.IntervalCuts.prefixDegree_succ,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor_zero_cons,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor_succ_cons,
      `SerrePositivity.EInfinity.IntervalCuts.tensorBoundaryTerm_eq_endpoints,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor_eraseCut_left,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor_eraseCut_right,
      `SerrePositivity.EInfinity.IntervalCuts.cut_factor_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.original_cut_iff_no_same_side_repeat,
      `SerrePositivity.EInfinity.IntervalCuts.CutDeletionDefect,
      `SerrePositivity.EInfinity.IntervalCuts.cutDeletionDefect_exists_iff,
      `SerrePositivity.EInfinity.IntervalCuts.cutDeletionDefect_unique,
      `SerrePositivity.EInfinity.IntervalCuts.erase_partner_edgeNondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.residual_partner_existsUnique,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap_swap,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap_ne,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swapEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap_output,
      `SerrePositivity.EInfinity.IntervalCuts.residualCutBasisWord,
      `SerrePositivity.EInfinity.IntervalCuts.residualCut_output_family,
      `SerrePositivity.EInfinity.IntervalCuts.residualCut_tensor_eq,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionSign_erase_same_color,
      `SerrePositivity.EInfinity.IntervalCuts.caesura_erase_final,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_erase_final,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.pivot_not_caesura,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap_coefficient,
      `SerrePositivity.EInfinity.IntervalCuts.nonpivotResidualCut_weighted_sum,
      `SerrePositivity.EInfinity.IntervalCuts.residualCut_tensor_sum_eq_zero,
      `SerrePositivity.EInfinity.IntervalCuts.edgeNondegenerate_between,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_pivot_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_pivot_endpoint_one,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_pivot_endpoint_zero,
      `SerrePositivity.EInfinity.IntervalCuts.pivotBoundary_gap_difference,
      `SerrePositivity.EInfinity.IntervalCuts.pivotBoundaryValue_sum,
      `SerrePositivity.EInfinity.IntervalCuts.pivotBoundaryValue_sum_zeroDegree,
      `SerrePositivity.EInfinity.IntervalCuts.GapNondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.gap_before_defect_existsUnique,
      `SerrePositivity.EInfinity.IntervalCuts.gap_after_defect_existsUnique,
      `SerrePositivity.EInfinity.IntervalCuts.erase_pivot_iff_gap_before,
      `SerrePositivity.EInfinity.IntervalCuts.erase_pivot_iff_gap_after,
      `SerrePositivity.EInfinity.IntervalCuts.pivotEraseBasisWord,
      `SerrePositivity.EInfinity.IntervalCuts.pivotErase_tensor_before,
      `SerrePositivity.EInfinity.IntervalCuts.pivotErase_tensor_after,
      `SerrePositivity.EInfinity.IntervalCuts.positionRank_gap_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.caesuraRank_gap_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.activePositions_erase_final_pivot_image,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_coefficient_before,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_coefficient_after,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_weighted_before,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_weighted_after,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_weighted_pair,
      `SerrePositivity.EInfinity.IntervalCuts.PivotResidualCut,
      `SerrePositivity.EInfinity.IntervalCuts.PivotResidualCut.sum_split,
      `SerrePositivity.EInfinity.IntervalCuts.PivotResidualCut.beforeEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.PivotResidualCut.afterEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.pivotResidualValue_sum,
      `SerrePositivity.EInfinity.IntervalCuts.gap_sum_complement,
      `SerrePositivity.EInfinity.IntervalCuts.pivotResidualValue_sum_eq_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.word,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.nonpivotEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.pivotEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.sum_three,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_reduce,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_eq_zero_of_no_cut,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.fiberEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.sum_fibers,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_sum_subtype,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_generator,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_differentialOnWord,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_differentialOnWord_reduce,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_differentialOnWord_eq_zero_of_no_cut,
      `SerrePositivity.EInfinity.IntervalCuts.RepeatCutPair,
      `SerrePositivity.EInfinity.IntervalCuts.regularCutEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.RepeatCutPair.factorBoundary_eq_pair,
      `SerrePositivity.EInfinity.IntervalCuts.repeatPairFiberEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_regular,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_boundary_factors,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_d_positive,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_d_zero,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.input_degrees_unique,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.collapse_segments,
      `SerrePositivity.EInfinity.TableReduction.fuseBoundary_fst_dropLast,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_row_bounds,
      `SerrePositivity.EInfinity.Surjection.substitute_horizontal_no_slot,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_complete,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_none_between,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_count_take,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_count_take_succ,
      `SerrePositivity.EInfinity.TableReduction.fuseBoundary_in_context,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.horizontal_vertical_join,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.vertical_horizontal_join,
      `SerrePositivity.EInfinity.TableReduction.ReductionInterval.weightedVertices_vertex,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_first_eq_nil,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_in_context] do
    unless env.contains required do
      throwError "EInfinity の必要な宣言がありません: {required}"
  logInfo m!"EInfinity 公理監査成功: {declarations} 宣言。標準 3 公理のみ。"

-- BF §1.2.3 の符号・五項の削除式と零 arity の境界例を照合する。
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SerrePositivity.EInfinity.Surjection

private def bfWord : Fin 7 → Fin 4 := ![0, 2, 1, 0, 3, 1, 0]
example : Function.Surjective bfWord ∧ Nondegenerate bfWord := by decide
example : (fun i => deletionCoefficient bfWord i) = ![1, 0, -1, 1, 0, 1, -1] := by decide
example : Fintype.card (BasisWord 3 0) = 6 := by decide
example : Fintype.card (BasisWord 0 0) = 1 := by decide
example : Fintype.card (BasisWord 0 1) = 0 := by decide
example : Fintype.card (BasisWord 1 1) = 0 := by decide
example : differentialOnWord ℤ (⟨bfWord, by decide⟩ : BasisWord 4 3) =
    generator ℤ ![2, 1, 0, 3, 1, 0] - generator ℤ ![0, 2, 0, 3, 1, 0] +
      generator ℤ ![0, 2, 1, 3, 1, 0] + generator ℤ ![0, 2, 1, 0, 3, 0] -
      generator ℤ ![0, 2, 1, 0, 3, 1] := by
  have hs : (fun i => deletionCoefficient bfWord i) = ![1, 0, -1, 1, 0, 1, -1] := by decide
  have h0 : erase bfWord 0 = ![2, 1, 0, 3, 1, 0] := by decide
  have h2 : erase bfWord 2 = ![0, 2, 0, 3, 1, 0] := by decide
  have h3 : erase bfWord 3 = ![0, 2, 1, 3, 1, 0] := by decide
  have h5 : erase bfWord 5 = ![0, 2, 1, 0, 3, 0] := by decide
  have h6 : erase bfWord 6 = ![0, 2, 1, 0, 3, 1] := by decide
  unfold differentialOnWord
  dsimp only
  simp_rw [congrFun hs]
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, one_zsmul, zero_zsmul, neg_one_zsmul, zero_add]
  erw [h0, h2, h3, h5, h6]
  simp only [sub_eq_add_neg, add_assoc]

-- BF §1.3.1 の table の二項と他の行長の選択の退化を照合する。
open SerrePositivity.EInfinity SerrePositivity.EInfinity.TableReduction
private def bfTable : Fin 3 → Equiv.Perm (Fin 4) :=
  ![1, Equiv.swap 1 3, Equiv.swap 2 3]
private def bfSchedule₁ : Schedule 4 2 := ⟨![2, 1, 3], by decide⟩
private def bfSchedule₂ : Schedule 4 2 := ⟨![2, 2, 2], by decide⟩
example : reduceRows (rows bfTable bfSchedule₁) [] = some [0, 1, 3, 1, 3, 2] := by decide
example : reduceRows (rows bfTable bfSchedule₂) [] = some [0, 1, 3, 2, 1, 2] := by decide
example : ∀ r : Schedule 4 2,
    (match reduceRows (rows bfTable r) [] with
    | none => true
    | some xs => !((xs.zip xs.tail).all (fun p => p.1 != p.2)) ||
        xs == [0, 1, 3, 1, 3, 2] || xs == [0, 1, 3, 2, 1, 2]) = true := by decide
example : Fintype.card {r : Schedule 4 2 //
    reduceRows (rows bfTable r) [] = some [0, 1, 3, 1, 3, 2]} = 1 := by decide
example : Fintype.card {r : Schedule 4 2 //
    reduceRows (rows bfTable r) [] = some [0, 1, 3, 2, 1, 2]} = 1 := by decide

-- BF §1.4.2 の復元候補の具体例と table の唯一の非退化出力を照合する。
open SerrePositivity.EInfinity.Surjection SerrePositivity.EInfinity.TableReduction
private def canonicalFixture : BasisWord 4 2 := ⟨![0, 1, 3, 1, 3, 2], by decide⟩
example : rowStarts canonicalFixture = [0, 2, 3] := by decide
example : List.ofFn (fun i : Fin 3 =>
    List.ofFn (fun j => (canonicalVertices canonicalFixture i)⁻¹ j)) =
      [[0, 1, 3, 2], [0, 3, 1, 2], [0, 1, 3, 2]] := by
  simp only [canonicalVertices, canonicalPermutation_inv_list]
  decide
private def canonicalFixtureRows (r : Schedule 4 2) : List (List (Fin 4) × ℕ) :=
  List.ofFn (fun i =>
    (canonicalRow (List.ofFn canonicalFixture.val) (rowStart canonicalFixture i), (r.val i).val))
example : ∀ r : Schedule 4 2,
    (match reduceRows (canonicalFixtureRows r) [] with
    | none => true
    | some xs => !((xs.zip xs.tail).all (fun p => p.1 != p.2)) ||
        xs == [0, 1, 3, 1, 3, 2]) = true := by decide
example : Fintype.card {r : Schedule 4 2 //
    reduceRows (canonicalFixtureRows r) [] = some [0, 1, 3, 1, 3, 2]} = 1 := by decide

-- 最終末尾の相殺例。正しい削除後次数で元の項が非零であることも照合する。
private def terminalWord : BasisWord 2 0 := ⟨![0, 1], by decide⟩
private def terminalTable : Fin 2 → Equiv.Perm (Fin 2) := ![1, Equiv.swap 0 1]
private def terminalSchedule : Schedule 2 1 := ⟨![1, 2], by decide⟩
example : reduceRows (rows terminalTable terminalSchedule) [] = some [0, 1, 0] := by decide
example : reduceRows (rows terminalTable
    (deletionScheduleTransfer terminalSchedule 1 0 (by decide) (by decide))) [] =
      some [0, 1, 1] := by decide
private theorem terminalDeletionTerm_eq_neg :
    listDeletionTerm ℤ (d := 0) ([0, 1, 0] : List (Fin 2)) ⟨2, by decide⟩ =
    -listGenerator ℤ (d := 0) [0, 1] := by
  unfold listDeletionTerm
  have hc : deletionCoefficient
      (fun j : Fin ([0, 1, 0] : List (Fin 2)).length => ([0, 1, 0] : List (Fin 2))[j.val])
      ⟨2, by decide⟩ = -1 := by decide
  rw [hc]
  exact neg_one_zsmul _
example : listDeletionTerm ℤ (d := 0) ([0, 1, 0] : List (Fin 2)) ⟨2, by decide⟩ ≠ 0 := by
  have hv : List.ofFn terminalWord.val = ([0, 1] : List (Fin 2)) := by decide
  have hg : listGenerator ℤ (d := 0) [0, 1] = basis ℤ 2 0 (ULift.up terminalWord) := by
    rw [← hv, listGenerator_ofFn, generator_word]
  rw [terminalDeletionTerm_eq_neg, hg]
  exact neg_ne_zero.mpr ((basis ℤ 2 0).ne_zero _)

example : listDeletionTerm ℤ (d := 0) ([0, 1, 0] : List (Fin 2)) ⟨2, by decide⟩ +
    listDeletionTerm ℤ (d := 0) ([0, 1, 1] : List (Fin 2)) ⟨1, by decide⟩ = 0 := by
  rw [terminalDeletionTerm_eq_neg]
  have hc : deletionCoefficient
      (fun j : Fin ([0, 1, 1] : List (Fin 2)).length => ([0, 1, 1] : List (Fin 2))[j.val])
      ⟨1, by decide⟩ = 1 := by decide
  simp only [listDeletionTerm, hc, one_zsmul]
  exact neg_add_cancel _

-- 逆探索の通過・内部停止・最終延長停止を具体的な行で照合する。
private def releaseSkipRows : List (List (Fin 3) × ℕ) := [([1, 0, 2], 1), ([2, 0, 1], 2)]
example : ReleaseSearch (0 : Fin 3) releaseSkipRows [] [([1, 0, 2], 1)] [[1]] []
    ([2, 0, 1], 2) [] := by
  exact .skip (by decide) (by decide) (by decide) (.hit (by decide))
example : reduceRows releaseSkipRows [0] = some [1, 2, 1] := by decide
example : reduceRows [([1, 0, 2], 1), ([2, 0, 1], 3)] ([] : List (Fin 3)) =
    some [1, 2, 0, 1] := by decide
example : ([1, 2, 0, 1] : List (Fin 3)).eraseIdx 2 = [1, 2, 1] := by decide
example : ReleaseSearch (0 : Fin 2) [([1, 0], 1)] [] [] [] [] ([1, 0], 1) [] := by
  exact .terminal (by decide) (by decide)
example : reduceRows [([1, 0], 1)] ([0] : List (Fin 2)) = some [1] := by decide
example : reduceRows [([1, 0], 2)] ([] : List (Fin 2)) = some [1, 0] := by decide

-- 実際の逆 Schedule の入力は退化出力の残余行末も含む。
private def reverseTerminalSchedule : Schedule 2 1 := ⟨![2, 1], by decide⟩
example : Nonempty (ReverseTransferData terminalTable reverseTerminalSchedule
    [0, 1, 1] ⟨1, by decide⟩) := by
  apply reverseTransferData_nonempty terminalTable reverseTerminalSchedule
    [0, 1, 1] (by decide) ⟨1, by decide⟩ (by decide) (by decide)
example : reduceRows (rows terminalTable
    (deletionScheduleTransfer reverseTerminalSchedule 0 1 (by decide) (by decide))) [] =
      some [0, 1, 0] := by decide

-- 一般の全単射・全残余相殺・微分保存・平方零を具体例でも元の型で適用する。
noncomputable example : FinalDeletion bfTable ≃ CaesuraDeletion bfTable := deletionEquiv bfTable
example : (∑ r : Schedule 4 2, remainderTerm ℤ bfTable r) = 0 :=
  sum_remainderTerm_zero ℤ bfTable
example : Surjection.differential ℤ 4 1 (onSequence ℤ bfTable) = vertexBoundary ℤ bfTable :=
  differential_onSequence_eq_vertexBoundary ℤ bfTable
example : (Surjection.differential ℤ 4 0).comp (Surjection.differential ℤ 4 1) = 0 :=
  differential_comp_differential ℤ 4 0
example : (chainMap ℤ 0).f 1 = ModuleCat.ofHom (normalizedMap ℤ 0 1) := chainMap_f ℤ 0 1

-- BF §1.2.6 の三つの合成語と符号 +,−,− を零始まりで照合する。
private def compositionOuter : BasisWord 3 1 := ⟨![0, 1, 0, 2], by decide⟩
private def compositionInner : BasisWord 2 1 := ⟨![0, 1, 0], by decide⟩
private def compositionCut₁ : OverlapPartition (occurrenceCount compositionOuter.val 0) 3 := by
  change OverlapPartition 2 3
  exact ⟨![1, 3], by decide⟩
private def compositionCut₂ : OverlapPartition (occurrenceCount compositionOuter.val 0) 3 := by
  change OverlapPartition 2 3
  exact ⟨![2, 2], by decide⟩
private def compositionCut₃ : OverlapPartition (occurrenceCount compositionOuter.val 0) 3 := by
  change OverlapPartition 2 3
  exact ⟨![3, 1], by decide⟩
example : Fintype.card (OverlapPartition 2 3) = 3 := by decide
example : compositeWord compositionOuter compositionInner 0 compositionCut₁ =
    [0, 2, 0, 1, 0, 3] := by decide
example : compositeWord compositionOuter compositionInner 0 compositionCut₂ =
    [0, 1, 2, 1, 0, 3] := by decide
example : compositeWord compositionOuter compositionInner 0 compositionCut₃ =
    [0, 1, 0, 2, 0, 3] := by decide
example : compositionSign compositionOuter compositionInner 0 compositionCut₁ = 1 := by decide
example : compositionSign compositionOuter compositionInner 0 compositionCut₂ = -1 := by decide
example : compositionSign compositionOuter compositionInner 0 compositionCut₃ = -1 := by decide
example : Fintype.card (OverlapPartition 2 0) = 0 := by decide
private def emptyCompositionWord : BasisWord 0 0 := ⟨Fin.elim0, by decide⟩
example : compositionOnWords ℤ compositionInner emptyCompositionWord 0 = 0 :=
  compositionOnWords_nullary_of_count_ne_one ℤ _ _ _ (by decide)
example : Surjection.partialComposition ℤ 2 2 1 1 0
    (basis ℤ 3 1 (ULift.up compositionOuter))
    (basis ℤ 2 1 (ULift.up compositionInner)) =
      compositionOnWords ℤ compositionOuter compositionInner 0 :=
  partialComposition_basis ℤ _ _ _

-- BF §1.5.4–6 の候補経路が、三項の合成語と同じ符号を持つ。
example :
    ((compositionPath compositionOuter compositionInner 0 compositionCut₁).sign : ℤ) = 1 := by
  rw [compositionPath_sign]
  decide
example :
    ((compositionPath compositionOuter compositionInner 0 compositionCut₂).sign : ℤ) = -1 := by
  rw [compositionPath_sign]
  decide
example :
    ((compositionPath compositionOuter compositionInner 0 compositionCut₃).sign : ℤ) = -1 := by
  rw [compositionPath_sign]
  decide
example : compositeGenerator ℤ compositionOuter compositionInner 0 compositionCut₁ =
    basis ℤ 4 2 (ULift.up (compositeBasisWord compositionOuter compositionInner 0 compositionCut₁
      (by decide))) := compositeGenerator_eq_basis ℤ _ _ _ _ (by decide)
example : (∑ i : Fin 2, segmentDegree compositionInner.val compositionCut₂ i) = 1 :=
  sum_segmentDegree compositionInner compositionCut₂ (by decide)
example : (∑ i : Fin 3, outerSegmentDegree compositionOuter.val 0 i.val) = 1 :=
  sum_outerSegmentDegree compositionOuter 0

-- 内外の非自明な逆置換行と除外文字、および空の内側行を照合する。
private def rowOuter : Equiv.Perm (Fin 3) := Equiv.swap 0 2
private def rowInner : Equiv.Perm (Fin 2) := Equiv.swap 0 1
example : List.ofFn rowOuter.symm = [2, 1, 0] := by decide
example : List.ofFn rowInner.symm = [1, 0] := by decide
example : substitute (n := 2) (1 : Fin 3) [2, 1, 0] [[1, 0]] = [3, 2, 1, 0] := by
  decide
example : available (compositionRemoved (1 : Fin 3) [2] [1])
    (List.ofFn (BarrattEccles.permutationComposition 2 2 1 rowOuter rowInner).symm) =
      [1, 0] := by
  rw [permutationComposition_available_substitute rowOuter rowInner 1 [2] [1] (by decide)]
  decide
example : List.ofFn
    (BarrattEccles.permutationComposition 2 0 1 rowOuter (1 : Equiv.Perm (Fin 0))).symm =
      [1, 0] := by
  rw [permutationComposition_inverse_row_substitute rowOuter (1 : Equiv.Perm (Fin 0)) 1]
  decide

-- 三種類の実際の二行抽出で、選択行の末尾を次行に残すことを確認する。
private def rowPre : List {a : Fin 3 // a ≠ 1} := [⟨2, by decide⟩]
private def rowPost : List {a : Fin 3 // a ≠ 1} := [⟨0, by decide⟩]
private def rowComposite : List (Fin 4) :=
  List.ofFn (BarrattEccles.permutationComposition 2 2 1 rowOuter rowInner).symm
private lemma rowComposite_available :
    available (compositionStateRemoved (1 : Fin 3) [] ([] : List (Fin 2))) rowComposite =
      substitute 1 (rowPre.map Subtype.val ++ 1 :: rowPost.map Subtype.val) [[1, 0]] := by
  rw [rowComposite, permutationComposition_state_available_substitute]
  decide
example : reduceRows [(rowComposite, 1), (rowComposite, 1)]
    (compositionStateRemoved (1 : Fin 3) [] ([] : List (Fin 2))) = some [3, 3] := by
  exact compositionExtractionStep_before (m := 2) (n := 2)
    1 [] [] [1, 0] rowPre rowPost rowComposite 1
    [(rowComposite, 1)] [3] rowComposite_available (by decide) (by decide) (by decide)
example : reduceRows [(rowComposite, rowPre.length + 2), (rowComposite, 1)]
    (compositionStateRemoved (1 : Fin 3) [] ([] : List (Fin 2))) = some [3, 2, 1, 1] := by
  exact compositionExtractionStep_inside (m := 2) (n := 2)
    1 [] [] [1, 0] rowPre rowPost rowComposite 2
    [(rowComposite, 1)] [1] rowComposite_available (by decide) (by decide) (by decide)
example : reduceRows [(rowComposite, rowPre.length + 2 + 1), (rowComposite, 1)]
    (compositionStateRemoved (1 : Fin 3) [] ([] : List (Fin 2))) = some [3, 2, 1, 0, 0] := by
  exact compositionExtractionStep_after (m := 2) (n := 2)
    1 [] [] [1, 0] rowPre rowPost rowComposite 1
    [(rowComposite, 1)] [0] rowComposite_available (by decide) (by decide)
    (by intro b; fin_cases b <;> decide) (by decide)
example : available (compositionStateRemoved (1 : Fin 3) [1] ([] : List (Fin 2)))
    rowComposite = [3, 0] := by
  rw [rowComposite, permutationComposition_state_available_substitute]
  decide

-- BF の実際の成功表の行末・一文字行・最終行と、同じ行を共有する成分端点を照合する。
private lemma rankFixture_success :
    reduceRows (rows bfTable bfSchedule₁) [] = some (List.ofFn canonicalFixture.val) := by
  decide
example : lineRank canonicalFixture.val (scheduleOffset bfSchedule₁ 0 + 1) = 0 :=
  lineRank_schedule_of_reduction bfTable bfSchedule₁ canonicalFixture.val
    rankFixture_success 0 1 (by decide)
example : lineRank canonicalFixture.val (scheduleOffset bfSchedule₁ 1 + 0) = 1 :=
  lineRank_schedule_of_reduction bfTable bfSchedule₁ canonicalFixture.val
    rankFixture_success 1 0 (by decide)
example : lineRank canonicalFixture.val (scheduleOffset bfSchedule₁ 2 + 2) = 2 :=
  lineRank_schedule_of_reduction bfTable bfSchedule₁ canonicalFixture.val
    rankFixture_success 2 2 (by decide)
example : reductionRow bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 2 = 1 := by
  apply (reductionRow_eq_iff bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 2 1).mpr
  decide
private def rankFixtureCuts : OverlapPartition 2 6 := ⟨![3, 4], by decide⟩
example : segmentDegree canonicalFixture.val rankFixtureCuts 0 = 1 := by
  rw [segmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0]
  decide
example : segmentDegree canonicalFixture.val rankFixtureCuts 1 = 1 := by
  rw [segmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 1]
  decide
-- 隣接重複を含む成功出力でも行内位置の番号は同じ定理で計算する。
private def rankDegenerate : Fin 3 → Fin 2 := ![0, 1, 1]
example : lineRank rankDegenerate (scheduleOffset reverseTerminalSchedule 0 + 1) = 0 := by
  exact lineRank_schedule_of_reduction terminalTable reverseTerminalSchedule rankDegenerate
    (by decide) 0 1 (by decide)
example : lineRank rankDegenerate (scheduleOffset reverseTerminalSchedule 1 + 0) = 1 := by
  exact lineRank_schedule_of_reduction terminalTable reverseTerminalSchedule rankDegenerate
    (by decide) 1 0 (by decide)

example : outerSegmentDegree canonicalFixture.val 1 0 = 0 := by
  rw [outerSegmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture
    rankFixture_success 1 (by decide) 0]
  decide
example : outerSegmentDegree canonicalFixture.val 1 1 = 2 := by
  rw [outerSegmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture
    rankFixture_success 1 (by decide) 1]
  decide
example : outerSegmentDegree canonicalFixture.val 1 2 = 0 := by
  rw [outerSegmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture
    rankFixture_success 1 (by decide) 2]
  decide

example : StrictMono (fun j : Fin (occurrenceCount canonicalFixture.val 1) =>
    reductionRow bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (occurrenceAt canonicalFixture.val 1 j)) :=
  occurrence_reductionRow_strictMono bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 1
example : lineRank rankDegenerate 1 < lineRank rankDegenerate 2 := by
  have h : reduceRows (rows terminalTable reverseTerminalSchedule) [] =
      some (List.ofFn rankDegenerate) := by decide
  exact reductionRow_lt_of_repeat terminalTable reverseTerminalSchedule rankDegenerate h
    1 2 (by decide) (by decide)

-- 同じ元の成功から取り出した隣接 cursor は、実際の末尾以外の除外更新で接続する。
private noncomputable def cursorRowOne :
    ScheduleRowCursor bfTable bfSchedule₁ 1 (List.ofFn canonicalFixture.val) :=
  Classical.choice (scheduleRowCursor_nonempty bfTable bfSchedule₁ 1
    (List.ofFn canonicalFixture.val) rankFixture_success)
private noncomputable def cursorRowTwo :
    ScheduleRowCursor bfTable bfSchedule₁ 2 (List.ofFn canonicalFixture.val) :=
  Classical.choice (scheduleRowCursor_nonempty bfTable bfSchedule₁ 2
    (List.ofFn canonicalFixture.val) rankFixture_success)
example : cursorRowTwo.removed = cursorRowOne.removed ++
    (available cursorRowOne.removed (vertexRow bfTable 1)).take ((bfSchedule₁.val 1).val - 1) :=
  (ScheduleRowCursor.next_state 1 cursorRowOne cursorRowTwo).2
example : (available cursorRowTwo.removed (vertexRow bfTable 2))[1]'(by
    have := cursorRowTwo.bound; change 3 ≤ _ at this; omega) = 3 := by
  have h := cursorRowTwo.value (4 : Fin 6) ⟨1, by decide⟩ (by decide)
  exact h.symm.trans (by decide)
-- 元の第三行の内部からの再開と、同じ行の末尾からの再開を元の出力の末尾で検証する。
example : reduceRows ((vertexRow bfTable 2, 2) :: cursorRowTwo.after)
    (cursorRowTwo.removed ++ (available cursorRowTwo.removed (vertexRow bfTable 2)).take 1) =
      some [3, 2] := by
  have h := cursorRowTwo.remainder_success_eq_drop (4 : Fin 6) ⟨1, by decide⟩ (by decide)
  change reduceRows ((vertexRow bfTable 2, 2) :: cursorRowTwo.after)
    (cursorRowTwo.removed ++ (available cursorRowTwo.removed (vertexRow bfTable 2)).take 1) =
      some ((List.ofFn canonicalFixture.val).drop 4) at h
  have ho : (List.ofFn canonicalFixture.val).drop 4 = [3, 2] := by decide
  rw [ho] at h
  exact h
example : reduceRows ((vertexRow bfTable 2, 1) :: cursorRowTwo.after)
    (cursorRowTwo.removed ++ (available cursorRowTwo.removed (vertexRow bfTable 2)).take 2) =
      some [2] := by
  have h := cursorRowTwo.remainder_success_eq_drop (5 : Fin 6) ⟨2, by decide⟩ (by decide)
  change reduceRows ((vertexRow bfTable 2, 1) :: cursorRowTwo.after)
    (cursorRowTwo.removed ++ (available cursorRowTwo.removed (vertexRow bfTable 2)).take 2) =
      some ((List.ofFn canonicalFixture.val).drop 5) at h
  have ho : (List.ofFn canonicalFixture.val).drop 5 = [2] := by decide
  rw [ho] at h
  exact h
example : canonicalFixture.val 4 ∉
    (reductionCursor bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 4).removed :=
  reductionCursor_value_not_removed bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 4

-- BF の元の成功表から、二つの重なる複数行成分を追加の成功仮定なしに抽出する。
example : reduceRows
    (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      rankFixtureCuts (by decide) 0).part
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (rankFixtureCuts.startPosition (by decide) 0)) = some [0, 1, 3] := by
  have h := componentExtraction_success bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0
  have hw : rankFixtureCuts.segment canonicalFixture.val 0 = [0, 1, 3] := by decide
  rw [hw] at h
  exact h
example : reduceRows
    (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      rankFixtureCuts (by decide) 1).part
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (rankFixtureCuts.startPosition (by decide) 1)) = some [3, 1, 3, 2] := by
  have h := componentExtraction_success bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 1
  have hw : rankFixtureCuts.segment canonicalFixture.val 1 = [3, 1, 3, 2] := by decide
  rw [hw] at h
  exact h
example : (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0).part.length = 2 := by
  rw [componentExtraction_length]
  decide
-- 終成分が同じ元の最終行内に入る切断も、同じ構成で一行の成功証跡になる。
private def sameRowCuts : OverlapPartition 2 6 := ⟨![5, 2], by decide⟩
example : reduceRows
    (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      sameRowCuts (by decide) 1).part
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (sameRowCuts.startPosition (by decide) 1)) = some [3, 2] := by
  have h := componentExtraction_success bfTable bfSchedule₁ canonicalFixture rankFixture_success
    sameRowCuts (by decide) 1
  have hw : sameRowCuts.segment canonicalFixture.val 1 = [3, 2] := by decide
  rw [hw] at h
  exact h
example : (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    sameRowCuts (by decide) 1).part.length = 1 := by
  rw [componentExtraction_length]
  decide
-- 共有端点の状態を厳密に引き継ぎ、共有文字を両成分に含めたまま連結する。
example : reduceRows
    ((componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      rankFixtureCuts (by decide) 0).part ++
    (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      rankFixtureCuts (by decide) 1).part)
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (rankFixtureCuts.startPosition (by decide) 0)) = some [0, 1, 3, 3, 1, 3, 2] := by
  have ht := componentExtraction_adjacent_prefix bfTable bfSchedule₁ canonicalFixture
    rankFixture_success rankFixtureCuts (by decide) 0 1 (by decide)
  have hs := ht.append [] [] rfl
  simp only [List.append_nil, List.flatten_append, componentExtraction_word] at hs
  have hw : rankFixtureCuts.segment canonicalFixture.val 0 ++
      rankFixtureCuts.segment canonicalFixture.val 1 = [0, 1, 3, 3, 1, 3, 2] := by decide
  rw [hw] at hs
  exact hs
example : (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0).part.map Prod.fst =
      [vertexRow bfTable 0, vertexRow bfTable 1] := by
  have hs := (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0).source
  change (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0).part.map Prod.fst =
      (((rows bfTable bfSchedule₁).drop 0).take 2).map Prod.fst at hs
  have hw : (((rows bfTable bfSchedule₁).drop 0).take 2).map Prod.fst =
      [vertexRow bfTable 0, vertexRow bfTable 1] := by decide
  exact hs.trans hw

-- 指定値の二出現の間の外側成分は、元の三行全てを通って実際の部分語を返す。
example : reduceRows
    (outerComponentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      1 (by decide) 1).part
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (occurrenceBoundaryPosition canonicalFixture.val 1 (by decide) 1)) = some [1, 3, 1] := by
  have h := outerComponentExtraction_success bfTable bfSchedule₁ canonicalFixture
    rankFixture_success 1 (by decide) 1
  have hw : outerComponentWord canonicalFixture.val 1 1 = [1, 3, 1] := by decide
  rw [hw] at h
  exact h
example : (outerComponentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    1 (by decide) 1).part.length = 3 := by
  rw [outerComponentExtraction_length]
  decide

-- 元の内側成功表と元の外側の指定出現から、垂直成分を実際の合成行列で抽出する。
private lemma verticalInner_success : reduceRows (rows terminalTable terminalSchedule) [] =
    some (List.ofFn compositionInner.val) := by decide
private def verticalCuts : OverlapPartition 2 3 := ⟨![2, 2], by decide⟩
private noncomputable def verticalFirstBlock : List (List (Fin 5) × ℕ) :=
  fixedOuterRows (m := 3) (n := 2)
    (bfTable (reductionRow bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 1)) 1
    (componentExtraction terminalTable terminalSchedule compositionInner verticalInner_success
      verticalCuts (by decide) 0).weightedVertices
private noncomputable def verticalFirstInitial : List (Fin 5) :=
  compositionStateRemoved (m := 3) (n := 2) 1
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 1)
    (reductionRemoved terminalTable terminalSchedule compositionInner.val verticalInner_success
      (verticalCuts.startPosition (by decide) 0))
example : reduceRows verticalFirstBlock verticalFirstInitial = some [1, 2] := by
  have h := componentVerticalExtraction_success (m := 3) (n := 2)
    bfTable bfSchedule₁ canonicalFixture rankFixture_success 1 1 (by decide)
    terminalTable terminalSchedule compositionInner verticalInner_success
    verticalCuts (by decide) 0 [] [] rfl
  have hw : (verticalCuts.segment compositionInner.val 0).map
      (BarrattEccles.insertedPosition 3 2 1) = [1, 2] := by decide
  simpa only [verticalFirstBlock, verticalFirstInitial, List.append_nil, hw] using h

-- 共有頂点の同じ二行を融合すると、共有文字は一度だけ出力し、元の後続状態へつながる。
example : reduceRows [([0, 1, 2, 3], 4), ([3], 1)] ([] : List (Fin 4)) =
    some [0, 1, 2, 3, 3] := by
  have h := rowFusion_success ([] : List (Fin 4)) [0, 1, 2, 3] (by decide) 2 3
    (by decide) (by decide) (by decide) (by decide) [([3], 1)] [3] (by decide)
  exact h

-- 未選択の内側文字が残る状態で、元の外側の零次数・正次数の水平成分を抽出する。
private noncomputable def horizontalFixtureBlock
    (i : Fin (occurrenceCount canonicalFixture.val 1)) : List (List (Fin 5) × ℕ) :=
  fixedInnerRows (m := 3) (n := 2)
    (terminalTable (reductionRow terminalTable terminalSchedule compositionInner.val
      verticalInner_success 0)) 1
    (outerComponentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      1 (by decide) i.val).weightedVertices
private noncomputable def horizontalFixtureInitial
    (i : Fin (occurrenceCount canonicalFixture.val 1)) : List (Fin 5) :=
  compositionStateRemoved (m := 3) (n := 2) 1
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (occurrenceBoundaryPosition canonicalFixture.val 1 (by decide) i.val))
    (reductionRemoved terminalTable terminalSchedule compositionInner.val verticalInner_success 0)
example : reduceRows (horizontalFixtureBlock ⟨0, by decide⟩)
    (horizontalFixtureInitial ⟨0, by decide⟩) = some [0, 1] := by
  have h := componentHorizontalExtraction_success (m := 3) (n := 2)
    bfTable bfSchedule₁ canonicalFixture rankFixture_success 1 ⟨0, by decide⟩
    terminalTable terminalSchedule compositionInner verticalInner_success 0 [] [] rfl
  have hw : (outerComponentWord canonicalFixture.val 1 0).map
      (horizontalLabel (m := 3) (n := 2) 1 (compositionInner.val 0)) = [0, 1] := by decide
  simpa only [horizontalFixtureBlock, horizontalFixtureInitial, List.append_nil, hw] using h
example : reduceRows (horizontalFixtureBlock ⟨1, by decide⟩)
    (horizontalFixtureInitial ⟨1, by decide⟩) =
    some [1, 4, 1] := by
  have h := componentHorizontalExtraction_success (m := 3) (n := 2)
    bfTable bfSchedule₁ canonicalFixture rankFixture_success 1 ⟨1, by decide⟩
    terminalTable terminalSchedule compositionInner verticalInner_success 0 [] [] rfl
  have hw : (outerComponentWord canonicalFixture.val 1 1).map
      (horizontalLabel (m := 3) (n := 2) 1 (compositionInner.val 0)) = [1, 4, 1] := by decide
  simpa only [horizontalFixtureBlock, horizontalFixtureInitial, List.append_nil, hw] using h

-- 元の内側成功表の最終位置では未選択の内側文字がなく、末尾一文字だけが残る。
example : available
    (reductionRemoved terminalTable terminalSchedule compositionInner.val verticalInner_success 2)
    (List.ofFn (terminalTable (reductionRow terminalTable terminalSchedule compositionInner.val
      verticalInner_success 2)).symm) = [0] := by
  have h := reductionRemoved_last_singleton terminalTable terminalSchedule compositionInner
    verticalInner_success 2 (by decide)
  have hv : compositionInner.val 2 = 0 := by decide
  rw [hv] at h
  exact h
private noncomputable def finalHorizontalBlock : List (List (Fin 5) × ℕ) :=
  fixedInnerRows (m := 3) (n := 2)
    (terminalTable (reductionRow terminalTable terminalSchedule compositionInner.val
      verticalInner_success 2)) 1
    (outerComponentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      1 (by decide) (occurrenceCount canonicalFixture.val 1)).weightedVertices
private noncomputable def finalHorizontalInitial : List (Fin 5) :=
  compositionStateRemoved (m := 3) (n := 2) 1
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (occurrenceBoundaryPosition canonicalFixture.val 1 (by decide)
        (occurrenceCount canonicalFixture.val 1)))
    (reductionRemoved terminalTable terminalSchedule compositionInner.val verticalInner_success 2)
example : reduceRows finalHorizontalBlock finalHorizontalInitial = some [1, 4, 3] := by
  have h := finalHorizontalExtraction_success (m := 3) (n := 2)
    bfTable bfSchedule₁ canonicalFixture rankFixture_success 1
    terminalTable terminalSchedule compositionInner verticalInner_success 2 (by decide) [] [] rfl
  have hw : (outerComponentWord canonicalFixture.val 1 (occurrenceCount canonicalFixture.val 1)).map
      (horizontalLabel (m := 3) (n := 2) 1 (compositionInner.val 2)) = [1, 4, 3] := by decide
  simpa only [finalHorizontalBlock, finalHorizontalInitial, List.append_nil, hw] using h
-- 指定値を行内部で最終除外し、最後の内側文字も除外した状態で後続へ接続する。
example : reduceRows
    [(List.ofFn (BarrattEccles.permutationComposition 2 2 1 1 rowInner).symm, 3), ([1, 3], 1)]
    (compositionStateRemoved (m := 2) (n := 2) 1 [] [1]) = some [0, 1, 3, 3] := by
  have h := singletonHorizontalStep_success (m := 2) (n := 2)
    1 rowInner 1 [] [1] 0 (by decide) 3 (by decide) (by decide) [([1, 3], 1)] [3] (by decide)
  exact h
-- 元の表の途中の共有行も同じ位置計算で融合し、先行出力は保つ。
example : reduceRows [([4], 1), ([0, 1, 2, 3], 4), ([3], 1)] ([] : List (Fin 5)) =
    some [4, 0, 1, 2, 3, 3] := by
  have h : reduceRows ([([4], 1)] ++
      ([0, 1, 2, 3], 2) :: ([0, 1, 2, 3], 3) :: [([3], 1)]) ([] : List (Fin 5)) =
        some [4, 0, 1, 1, 2, 3, 3] := by decide
  exact rowFusion_in_context [([4], 1)] [] [0, 1, 2, 3] (by decide) 2 3 [([3], 1)]
    [4, 0, 1, 1, 2, 3, 3] h

-- 元の二つの成功だけから、全ての水平・垂直成分を含む表の成功を導く。
private def fullCompositionFixture : TableCompositionData 3 2 2 1 where
  outer := bfTable
  outerSchedule := bfSchedule₁
  outerWord := canonicalFixture
  outer_success := rankFixture_success
  inner := terminalTable
  innerSchedule := terminalSchedule
  innerWord := compositionInner
  inner_success := verticalInner_success
  slot := 1
  cuts := by change OverlapPartition 2 3; exact verticalCuts
  inner_positive := by decide
example : reduceRows (fullCompositionFixture.rawRows 0) [] =
    some [0, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3] := by
  have hw : fullCompositionFixture.rawWord 0 = [0, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3] := by
    rw [TableCompositionData.rawWord,
      dite_eq_left (show 0 < fullCompositionFixture.count by decide),
      TableCompositionData.rawWord, dite_eq_left (show 1 < fullCompositionFixture.count by decide),
      TableCompositionData.rawWord,
      dite_eq_right (show ¬2 < fullCompositionFixture.count by decide)]
    decide
  simpa only [hw] using fullCompositionFixture.raw_success_zero

-- 全表の両種類の共有境界は、元の成功表の同じ実際の置換行を共有する。
example : ((fullCompositionFixture.horizontalRows 0).map Prod.fst).getLast? =
    ((fullCompositionFixture.verticalRows ⟨0, by decide⟩).map Prod.fst).head? :=
  fullCompositionFixture.horizontal_vertical_join ⟨0, by decide⟩
example : ((fullCompositionFixture.verticalRows ⟨1, by decide⟩).map Prod.fst).getLast? =
    ((fullCompositionFixture.horizontalRows 2).map Prod.fst).head? :=
  fullCompositionFixture.vertical_horizontal_join ⟨1, by decide⟩

-- 全共有行の融合後は、四つの重複境界文字を消した実際の合成語を返す。
private lemma fusedFixture_word : fullCompositionFixture.fusedWord 0 =
    [0, 1, 2, 4, 2, 1, 4, 3] := by
  rw [fullCompositionFixture.fusedWord_step ⟨0, by decide⟩,
    fullCompositionFixture.fusedWord_step ⟨1, by decide⟩,
    TableCompositionData.fusedWord,
    dite_eq_right (show ¬2 < fullCompositionFixture.count by decide)]
  decide
example : reduceRows (fullCompositionFixture.fusedRows 0) [] =
    some [0, 1, 2, 4, 2, 1, 4, 3] := by
  simpa only [fusedFixture_word] using fullCompositionFixture.fused_success_zero

-- 行長の古典選択を使わず、元の全成分語だけで融合出力を計算する。
private lemma blockFixture_word : fullCompositionFixture.blockWord 0 =
    [0, 1, 2, 4, 2, 1, 4, 3] := by
  rw [TableCompositionData.blockWord,
    dite_eq_left (show 0 < fullCompositionFixture.count by decide),
    TableCompositionData.blockWord,
    dite_eq_left (show 1 < fullCompositionFixture.count by decide),
    TableCompositionData.blockWord,
    dite_eq_right (show ¬2 < fullCompositionFixture.count by decide)]
  decide
example : reduceRows (fullCompositionFixture.fusedRows 0) [] =
    some [0, 1, 2, 4, 2, 1, 4, 3] := by
  simpa only [blockFixture_word] using fullCompositionFixture.fused_success_blockWord
example : fullCompositionFixture.fusedWord 0 = fullCompositionFixture.blockWord 0 :=
  fullCompositionFixture.fusedWord_eq_blockWord 0 (by decide)
-- 前半が二つの指定値を含むとき、後半は実際に二つの部分語を消費して始まる。
example : substitute (m := 1) (n := 2) 0 ([0, 1, 0] ++ [0, 1]) [[0], [1], [0, 1]] =
    substitute (m := 1) (n := 2) 0 [0, 1, 0] [[0], [1], [0, 1]] ++
      substitute (m := 1) (n := 2) 0 [0, 1] [[0, 1]] := by
  have hc : ([0, 1, 0] : List (Fin 2)).count 0 = 2 := by decide
  have h := substitute_append (m := 1) (n := 2) 0 [0, 1, 0] [0, 1] [[0], [1], [0, 1]]
  rw [hc] at h
  exact h

-- 二番目の指定値以前に一個、自身まで含めると二個の部分語を消費する。
example : ((List.ofFn canonicalFixture.val).take 3).count 1 = 1 := by
  have hp : (occurrenceAt canonicalFixture.val 1 ⟨1, by decide⟩).val = 3 := by decide
  simpa only [hp] using occurrenceAt_count_take canonicalFixture.val 1 ⟨1, by decide⟩
example : ((List.ofFn canonicalFixture.val).take 4).count 1 = 2 := by
  have hp : (occurrenceAt canonicalFixture.val 1 ⟨1, by decide⟩).val = 3 := by decide
  simpa only [hp] using occurrenceAt_count_take_succ canonicalFixture.val 1 ⟨1, by decide⟩
-- 隣接する出現の間の水平文字は指定値と異なる。
example : canonicalFixture.val 2 ≠ 1 :=
  occurrenceAt_none_between canonicalFixture.val 1 ⟨0, by decide⟩ ⟨1, by decide⟩ rfl 2
    (by decide) (by decide)
-- 第二出現の代入では第二部分語を使い、その後へ残りの部分語を渡す。
example : substitute (n := 2) 1 (List.ofFn canonicalFixture.val) [[0, 1], [1, 0]] =
    substitute (n := 2) 1 ((List.ofFn canonicalFixture.val).take 3) [[0, 1], [1, 0]] ++
      [2, 1] ++ substitute (n := 2) 1 ((List.ofFn canonicalFixture.val).drop 4) [] := by
  have hp : (occurrenceAt canonicalFixture.val 1 ⟨1, by decide⟩).val = 3 := by decide
  have h := substitute_at_occurrence (n := 2) canonicalFixture.val 1 ⟨1, by decide⟩
    [[0, 1], [1, 0]]
  rw [hp] at h
  exact h

-- 実際の重なる分割でも、第二出現の挿入部分は同じ番号の垂直語になる。
example : compositeWord canonicalFixture compositionInner 1 verticalCuts =
    substitute (n := 2) 1 ((List.ofFn canonicalFixture.val).take 3)
      (verticalCuts.segments compositionInner.val) ++
        (verticalCuts.segment compositionInner.val ⟨1, by decide⟩).map
          (BarrattEccles.insertedPosition 3 2 1) ++
            substitute (n := 2) 1 ((List.ofFn canonicalFixture.val).drop 4) [] := by
  have hp : (occurrenceAt canonicalFixture.val 1 ⟨1, by decide⟩).val = 3 := by decide
  have h := compositeWord_at_occurrence canonicalFixture compositionInner 1 verticalCuts
    ⟨1, by decide⟩
  rw [hp] at h
  exact h

-- 最初の融合水平部分は、最初の指定値以前の実際の代入と一致する。
example : (fullCompositionFixture.horizontalWord 0).dropLast = [0] := by
  exact fullCompositionFixture.firstHorizontal_dropLast.trans (by decide)

-- 中間・最終水平語と共有垂直末尾を、元の成分から一般定理で計算する。
example : (fullCompositionFixture.horizontalWord 1).dropLast = [2, 4] := by
  exact (fullCompositionFixture.middleHorizontal_dropLast ⟨0, by decide⟩ ⟨1, by decide⟩ rfl).trans
    (by decide)
example : fullCompositionFixture.horizontalWord 2 = [1, 4, 3] := by
  exact (fullCompositionFixture.finalHorizontal_word ⟨1, by decide⟩ (by decide)).trans (by decide)
-- 共有境界を全部融合した実際の表が、元のリスト代入による合成語を返す。
example : fullCompositionFixture.blockWord 0 =
    compositeWord canonicalFixture compositionInner 1 verticalCuts :=
  fullCompositionFixture.blockWord_eq_compositeWord
example : reduceRows (fullCompositionFixture.fusedRows 0) [] =
    some (compositeWord canonicalFixture compositionInner 1 verticalCuts) :=
  fullCompositionFixture.fused_success_compositeWord

-- 次数 2 と次数 1 の元の二表から、融合後は四行・総選択長八の実際の Schedule を得る。
example : (fullCompositionFixture.fusedRows 0).length = 4 :=
  fullCompositionFixture.fusedRows_length
example : (∑ i, fullCompositionFixture.fusedLength i) = 8 :=
  fullCompositionFixture.fusedLength_sum
example : (∑ i, (fullCompositionFixture.fusedSchedule.val i).val) = 8 :=
  fullCompositionFixture.fusedSchedule.property.2
example : ∀ i, 0 < (fullCompositionFixture.fusedSchedule.val i).val :=
  fullCompositionFixture.fusedSchedule.property.1
example (i : Fin 4) : fullCompositionFixture.fusedLength i ≤ 5 :=
  (fullCompositionFixture.fusedLength_bounds i).2

-- 実際の経路連結の共有頂点は一度だけ残る。
example : DegreePath.vertices (DegreePath.append (DegreePath.horizontal 1)
    (DegreePath.vertical 2)) = [(0, 0), (1, 0), (1, 1), (1, 2)] := by
  rw [DegreePath.vertices_append, DegreePath.vertices_horizontal, DegreePath.vertices_vertical]
  decide
example : DegreePath.vertices (DegreePath.corner 0 0) = [(0, 0)] := by
  exact (DegreePath.vertices_corner 0 0).trans (by decide)
-- 最初の水平次数零・後の垂直次数零を含む実際の compositionPath の全頂点。
private lemma compositionFixture_vertices :
    DegreePath.vertices (compositionPath canonicalFixture compositionInner 1 verticalCuts) =
      [(0, 0), (0, 1), (1, 1), (2, 1)] := by
  have hh : outerSegmentDegree canonicalFixture.val 1 0 = 0 := by decide
  have hp : compositionDegreePairs canonicalFixture compositionInner 1 verticalCuts =
      [(1, 2), (0, 0)] := by decide
  have h := compositionPath_vertices canonicalFixture compositionInner 1 verticalCuts
  rw [hh, hp] at h
  apply h.trans
  simp only [DegreePath.blockVertices]
  decide

-- 元の所属行から作った融合格子列は同じ全頂点列を持つ。
private lemma fusedFixture_vertices : fullCompositionFixture.fusedGridVertices 0 =
    [(0, 0), (0, 1), (1, 1), (2, 1)] := by
  rw [TableCompositionData.fusedGridVertices,
    dite_eq_left (show 0 < fullCompositionFixture.count by decide),
    TableCompositionData.fusedGridVertices,
    dite_eq_left (show 1 < fullCompositionFixture.count by decide),
    TableCompositionData.fusedGridVertices,
    dite_eq_right (show ¬2 < fullCompositionFixture.count by decide)]
  decide
-- 具体例では元の実際の経路置換列と構成済み Schedule で抽出成功する。
example : reduceRows (rows fullCompositionFixture.pathSequence fullCompositionFixture.fusedSchedule)
    [] = some (compositeWord canonicalFixture compositionInner 1 verticalCuts) := by
  exact fullCompositionFixture.pathSequence_success

-- 座標の一致は具体例の有限計算に頼らず一般定理からも得られる。
example : DegreePath.vertices (compositionPath canonicalFixture compositionInner 1 verticalCuts) =
    fullCompositionFixture.fusedGridVertices 0 :=
  fullCompositionFixture.compositionPath_vertices_eq_grid
-- 実際の構成済み経路 Schedule の正規化項は、期待した非退化合成語の生成元。
example : term ℤ fullCompositionFixture.pathSequence fullCompositionFixture.fusedSchedule =
    listGenerator ℤ [0, 1, 2, 4, 2, 1, 4, 3] := by
  have h := fullCompositionFixture.term_pathSequence ℤ
  have hw : compositeWord canonicalFixture compositionInner 1 verticalCuts =
      [0, 1, 2, 4, 2, 1, 4, 3] := by decide
  change term ℤ fullCompositionFixture.pathSequence fullCompositionFixture.fusedSchedule =
    listGenerator ℤ (compositeWord canonicalFixture compositionInner 1 verticalCuts) at h
  rw [hw] at h
  exact h

-- 連続重複だけを縮め、離れた同じ値は残す。
example : AdjacentCollapse.collapse ([0, 0, 1, 1, 0, 0] : List (Fin 2)) = [0, 1, 0] := by
  decide
-- 反復出現を含む実際の合成語から元の両語を一般定理で復元する。
example : CompositeRecovery.outerWord 1
    (compositeWord canonicalFixture compositionInner 1 verticalCuts) = [0, 1, 3, 1, 3, 2] := by
  exact (CompositeRecovery.outerWord_compositeWord canonicalFixture compositionInner 1
    verticalCuts (by decide)).trans (by decide)
example : (compositeWord canonicalFixture compositionInner 1 verticalCuts).filterMap
    (CompositeRecovery.innerLabel 1) = [0, 1, 1, 0] := by
  exact (CompositeRecovery.inner_compositeWord canonicalFixture compositionInner 1
    verticalCuts).trans (by decide)
example : CompositeRecovery.innerWord 1
    (compositeWord canonicalFixture compositionInner 1 verticalCuts) = [0, 1, 0] := by
  exact (CompositeRecovery.innerWord_compositeWord canonicalFixture compositionInner 1
    verticalCuts (by decide)).trans (by decide)

-- 出力だけから両分割部分語を共有端点も含めて復元する。
example : CompositeRecovery.partsOfWord 1
    (compositeWord canonicalFixture compositionInner 1 verticalCuts) = [[0, 1], [1, 0]] := by
  exact (CompositeRecovery.partsOfWord_compositeWord canonicalFixture compositionInner 1
    verticalCuts (by decide)).trans (by decide)
-- 分割復元は空の内側部分語もそのまま扱う。
example : CompositeRecovery.splitParts (m := 1) (n := 0) 0 [0, 1] [0] = [[]] := by
  exact CompositeRecovery.splitParts_substitute (m := 1) (n := 0) 0 [0, 1] [[]]
    (by decide) (by decide)
-- 同じ成功出力を与える元の Schedule は一意。
example (r : Schedule 4 2)
    (h : reduceRows (rows bfTable r) [] = some (List.ofFn canonicalFixture.val)) :
    r = bfSchedule₁ :=
  schedule_eq_of_same_output bfTable bfTable r bfSchedule₁ canonicalFixture.val h
    rankFixture_success

-- 実際の内側置換が変化する二行でも、非退化成功の前行末は内側にある。
example : ∃ b : Fin 2, (1 : Fin 4) = BarrattEccles.insertedPosition 2 2 1 b := by
  exact permutationComposition_vertical_endpoint_inserted
    (1 : Equiv.Perm (Fin 3)) (1 : Equiv.Perm (Fin 2)) (Equiv.swap 0 1)
    1 [] [0, 1, 2, 1, 3] 1 2 3 [] (by decide) (by decide) (by decide)
-- 同じ成功の更新後の次行先頭も内側にある。
example : ∃ b : Fin 2, (2 : Fin 4) = BarrattEccles.insertedPosition 2 2 1 b := by
  exact permutationComposition_vertical_next_head_inserted
    (1 : Equiv.Perm (Fin 3)) (1 : Equiv.Perm (Fin 2)) (Equiv.swap 0 1)
    1 [] [0, 1, 2, 1, 3] 1 2 2 3 [] (by decide) (by decide) (by decide) (by decide)

-- 最終行直前までの二行を、実際の合成成功から元の内側抽出へ射影する。
private def reverseVerticalEntries : List (Equiv.Perm (Fin 2) × ℕ) :=
  [(1, 2), (Equiv.swap 0 1, 1)]
private lemma reverseVerticalPrefix :
    ExtractionPrefix (verticalTable (1 : Equiv.Perm (Fin 3)) 1 reverseVerticalEntries)
      [] [[0, 1], [2]] [0] := by
  have he : verticalTable (1 : Equiv.Perm (Fin 3)) 1 reverseVerticalEntries =
      [([0, 1, 2, 3], 2), ([0, 2, 1, 3], 1)] := by decide
  rw [he]
  exact .cons (by decide) (by decide) (.cons (by decide) (by decide) (.nil _))
example : ExtractionPrefix ([([0, 1], 1), ([1, 0], 1)] : List (List (Fin 2) × ℕ))
    [] [[0], [1]] [] := by
  have hp := vertical_prefix_inner_projection (1 : Equiv.Perm (Fin 3)) 1
    reverseVerticalEntries (1 : Equiv.Perm (Fin 2)) 3 [] [] [0] [1, 2, 3] [[0, 1], [2]]
    reverseVerticalPrefix (by decide) (by decide)
  convert hp using 1 <;> decide

-- 外側文字で終わる最終行も内側末尾を残し、垂直成分全体を復元する。
example : ExtractionPrefix
    ([([0, 1], 1), ([1, 0], 1), ([0, 1], 2)] : List (List (Fin 2) × ℕ))
    [] [[0], [1], [0, 1]] [0] := by
  have hp := vertical_interval_inner_projection (1 : Equiv.Perm (Fin 3)) 1
    reverseVerticalEntries (1 : Equiv.Perm (Fin 2)) 3 [] [] [0] [1, 2, 3] [[0, 1], [2]]
    reverseVerticalPrefix (by decide) (by decide) (by decide)
  convert hp using 1 <;> decide
-- 同じ最終行の元の除外更新は内側選択語全体を除く。復元状態では末尾を残す。
example : (([1, 2, 3] : List (Fin 4)).take 2).filterMap
    (CompositeRecovery.innerLabel (m := 2) (n := 2) 1) =
    (([1, 2, 3] : List (Fin 4)).take 3).filterMap
      (CompositeRecovery.innerLabel (m := 2) (n := 2) 1) := by
  exact filterMap_selection_discarded_last (CompositeRecovery.innerLabel (m := 2) (n := 2) 1)
    [1, 2, 3] 3 (by decide) 3 (by decide) (by decide)

-- 内側文字が一つだけ除外されても、外側指定値はまだ可用である。
example : CompositeRecovery.outerRemoved (m := 2) (n := 2) 1 [1] = [] := by decide
-- 内側文字を全て除外した時点で、外側指定値も除外される。
example : CompositeRecovery.outerRemoved (m := 2) (n := 2) 1 [1, 2] = [1] := by decide
example : AdjacentCollapse.collapse
    ((available [1] (List.ofFn
      (BarrattEccles.permutationComposition 2 2 1 (1 : Equiv.Perm (Fin 3))
        (Equiv.swap 0 1)).symm)).map
        (CompositeRecovery.outerLabel (m := 2) (n := 2) 1)) = [0, 1, 2] := by
  exact (CompositeRecovery.outerLabel_available_composition_row 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 1) [1]).trans (by decide)
example : AdjacentCollapse.collapse
    ((available [1, 2] (List.ofFn
      (BarrattEccles.permutationComposition 2 2 1 (1 : Equiv.Perm (Fin 3))
        (Equiv.swap 0 1)).symm)).map
        (CompositeRecovery.outerLabel (m := 2) (n := 2) 1)) = [0, 2] := by
  exact (CompositeRecovery.outerLabel_available_composition_row 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 1) [1, 2]).trans (by decide)
-- 内側 arity 零では初期状態から指定値が消える。同じ一般定理を適用する。
example : CompositeRecovery.outerRemoved (m := 2) (n := 0) 1 [] = [1] := by decide
example : AdjacentCollapse.collapse
    ((available [] (List.ofFn
      (BarrattEccles.permutationComposition 2 0 1 (1 : Equiv.Perm (Fin 3))
        (1 : Equiv.Perm (Fin 0))).symm)).map
        (CompositeRecovery.outerLabel (m := 2) (n := 0) 1)) = [0, 2] := by
  exact (CompositeRecovery.outerLabel_available_composition_row 1
    (1 : Equiv.Perm (Fin 3)) (1 : Equiv.Perm (Fin 0)) []).trans (by decide)

-- 重複区間の途中で切った後続も、縮約後の対応順位へ戻る。
example : AdjacentCollapse.collapse (([0, 0, 1, 1, 0, 0] : List (Fin 2)).drop 3) =
    [1, 0] := by
  exact (AdjacentCollapse.collapse_drop_rank [0, 0, 1, 1, 0, 0] 3 (by decide)).trans
    (by decide)
private def outerRecoveryEntries :
    List (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2) × ℕ) :=
  [(1, 1, 2), (1, Equiv.swap 0 1, 1), (1, 1, 3)]
private lemma outerRecoveryPrefix : ExtractionPrefix
    (CompositeRecovery.mixedTable 1 outerRecoveryEntries) [] [[0, 1], [2], [1, 2, 3]]
    [0, 1, 2] := by
  have he : CompositeRecovery.mixedTable 1 outerRecoveryEntries =
      [([0, 1, 2, 3], 2), ([0, 2, 1, 3], 1), ([0, 1, 2, 3], 3)] := by decide
  rw [he]
  exact .cons (by decide) (by decide)
    (.cons (by decide) (by decide) (.cons (by decide) (by decide) (.nil _)))
-- 全合成抽出から復元した外側表は、垂直移動による同じ外側行をまだ保持する。
example : reduceRows
    ([([0, 1, 2], 2), ([0, 1, 2], 1), ([0, 1, 2], 2)] : List (List (Fin 3) × ℕ)) [] =
    some [0, 1, 1, 1, 2] := by
  have hp := CompositeRecovery.outer_prefix_success 1 outerRecoveryEntries [] [0, 1, 2]
    [[0, 1], [2], [1, 2, 3]] outerRecoveryPrefix [] [] rfl
  convert hp using 1 <;> decide

-- 外側の三重行を一行に融合し、共有文字は一度だけ数える。
example : compressRows
    ([([0, 1, 2], 2), ([0, 1, 2], 1), ([0, 1, 2], 2)] : List (List (Fin 3) × ℕ)) =
    [([0, 1, 2], 3)] := by decide
-- 離れた同じ行は融合しない。
example : (compressRows
    ([([0, 1], 1), ([1, 0], 1), ([0, 1], 1)] : List (List (Fin 2) × ℕ))).map Prod.fst =
    [[0, 1], [1, 0], [0, 1]] := by
  exact (compressRows_fst _).trans (by decide)
-- 実際の合成表から圧縮外側表と、その縮約出力の全体一致を得る。
example : ∃ picked finish out',
    ExtractionPrefix (CompositeRecovery.mixedTable 1 outerRecoveryEntries) [] picked finish ∧
      [0, 1, 2, 1, 2, 3] = picked.flatten ∧
      reduceRows (compressRows (CompositeRecovery.recoveredOuterTable 1
        outerRecoveryEntries picked)) [] = some out' ∧
      AdjacentCollapse.collapse out' = [0, 1, 2] := by
  have hs : reduceRows (CompositeRecovery.mixedTable 1 outerRecoveryEntries) [] =
      some [0, 1, 2, 1, 2, 3] := by
    simpa using outerRecoveryPrefix.append [] [] rfl
  obtain ⟨picked, finish, out', hp, ho, ht, hc⟩ :=
    CompositeRecovery.compressed_outer_table_success 1 outerRecoveryEntries [] _ hs
  refine ⟨picked, finish, out', hp, ho, ?_, hc.trans (by decide)⟩
  simpa only [CompositeRecovery.outerRemoved_nil (m := 2) (n := 2) 1 (by decide)] using ht

-- 前行末が内側、次行頭が外側の水平移動でも外側選択語の連結は非退化。
example : ([0, 1, 2, 1] : List (Fin 3)).IsChain (· ≠ ·) := by
  have hp := CompositeRecovery.horizontal_outer_selections_isChain 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 2) (1 : Equiv.Perm (Fin 2))
    [] [0, 1, 3, 1, 2] 2 3 [] (by decide) (by decide)
  convert hp using 1; decide
-- 前行末が外側、次行頭が内側の場合も同じ一般定理を使う。
example : ([0, 1, 0, 2] : List (Fin 3)).IsChain (· ≠ ·) := by
  have hp := CompositeRecovery.horizontal_outer_selections_isChain 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 1) (1 : Equiv.Perm (Fin 2))
    [] [0, 1, 2, 0, 3] 1 4 [] (by decide) (by decide)
  convert hp using 1; decide
-- 内側 arity 零も元の指定値を消した外側語の同じ境界定理に含む。
example : ([0, 2, 0] : List (Fin 3)).IsChain (· ≠ ·) := by
  have hp := CompositeRecovery.horizontal_outer_selections_isChain 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 2) (1 : Equiv.Perm (Fin 0))
    [] [0, 1, 0] 1 2 [] (by decide) (by decide)
  convert hp using 1; decide

-- 垂直・水平を交互に持つ実際の合成表から元の bfTable の Schedule まで戻す。
private def gridRecoveryEntries :
    List (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 2) × ℕ) :=
  [(1, 1, 2), (1, Equiv.swap 0 1, 1),
    (Equiv.swap 1 3, Equiv.swap 0 1, 1), (Equiv.swap 2 3, Equiv.swap 0 1, 4)]
private lemma gridRecoveryPrefix : ExtractionPrefix
    (CompositeRecovery.mixedTable 1 gridRecoveryEntries) []
    [[0, 1], [2], [4], [2, 1, 4, 3]] [0, 2, 1, 4] := by
  have he : CompositeRecovery.mixedTable 1 gridRecoveryEntries =
      [([0, 1, 2, 3, 4], 2), ([0, 2, 1, 3, 4], 1),
        ([0, 4, 3, 2, 1], 1), ([0, 2, 1, 4, 3], 4)] := by decide
  rw [he]
  exact .cons (by decide) (by decide) (.cons (by decide) (by decide)
    (.cons (by decide) (by decide) (.cons (by decide) (by decide) (.nil _))))
example : reduceRows (rows bfTable bfSchedule₁) [] = some [0, 1, 3, 1, 3, 2] := by
  have hsuccess : reduceRows (CompositeRecovery.mixedTable 1 gridRecoveryEntries) [] =
      some [0, 1, 2, 4, 2, 1, 4, 3] := by
    simpa using gridRecoveryPrefix.append [] [] rfl
  obtain ⟨picked, finish, hp, _, hs, _⟩ :=
    CompositeRecovery.compressed_outer_table_nondegenerate 1 gridRecoveryEntries [] _
      hsuccess (by decide) (by decide)
  obtain ⟨hwords, _⟩ := hp.unique gridRecoveryPrefix
  rw [hwords] at hs
  have htable : compressRows (CompositeRecovery.recoveredOuterTable 1 gridRecoveryEntries
      [[0, 1], [2], [4], [2, 1, 4, 3]]) = rows bfTable bfSchedule₁ := by decide
  rw [htable, CompositeRecovery.outerRemoved_nil (m := 3) (n := 2) 1 (by decide)] at hs
  convert hs using 1; decide

-- 同じ四行の例を実際の ShufflePath と Schedule から生成する。
private def gridRecoveryPath : BarrattEccles.ShufflePath 2 1 := ⟨{1, 2}, by decide⟩
private def gridRecoverySchedule : Schedule 5 3 := ⟨![2, 1, 1, 4], by decide⟩
example : AdjacentCollapse.collapse (List.ofFn (fun i =>
    (![0, 1, 0] : Fin 3 → Fin 2) (gridRecoveryPath.horizontal i))) = [0, 1, 0] := by
  exact (CompositeRecovery.collapse_horizontal_ofFn gridRecoveryPath _).trans (by decide)
example : ∃ table : List (List (Fin 4) × ℕ),
    reduceRows table [] = some [0, 1, 3, 1, 3, 2] ∧
      table.map Prod.fst = List.ofFn (fun j => List.ofFn (bfTable j).symm) ∧ table.length = 3 := by
  have hentries : CompositeRecovery.shuffleTableEntries gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule = gridRecoveryEntries := by decide
  have hsuccess : reduceRows (rows (fun i => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal i)) (terminalTable (gridRecoveryPath.vertical i)))
      gridRecoverySchedule) [] = some [0, 1, 2, 4, 2, 1, 4, 3] := by
    rw [← CompositeRecovery.shuffleTableEntries_rows 1 gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule, hentries]
    simpa using gridRecoveryPrefix.append [] [] rfl
  obtain ⟨picked, finish, _, _, hs, _, hrows, hlen⟩ :=
    CompositeRecovery.shuffle_outer_recovery_with_rows (by decide) 1 gridRecoveryPath
      bfTable terminalTable gridRecoverySchedule _ hsuccess (by decide)
  exact ⟨_, by convert hs using 1; decide, hrows, hlen⟩

-- 外側 Schedule を仮定せず実際の shuffle 成功から構成し、既知の Schedule との一致を証明する。
example : ∃ r : Schedule 4 2, r = bfSchedule₁ ∧
    reduceRows (rows bfTable r) [] = some (List.ofFn canonicalFixture.val) := by
  have hentries : CompositeRecovery.shuffleTableEntries gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule = gridRecoveryEntries := by decide
  have hsuccess : reduceRows (rows (fun i => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal i)) (terminalTable (gridRecoveryPath.vertical i)))
      gridRecoverySchedule) [] = some [0, 1, 2, 4, 2, 1, 4, 3] := by
    rw [← CompositeRecovery.shuffleTableEntries_rows 1 gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule, hentries]
    simpa using gridRecoveryPrefix.append [] [] rfl
  obtain ⟨r, hs, _, _⟩ := CompositeRecovery.shuffle_outer_schedule (by decide) 1
    gridRecoveryPath bfTable terminalTable gridRecoverySchedule _ hsuccess (by decide)
  have hw : CompositeRecovery.outerWord (m := 3) (n := 2) 1
      [0, 1, 2, 4, 2, 1, 4, 3] = List.ofFn canonicalFixture.val := by decide
  rw [hw] at hs
  exact ⟨r, schedule_eq_of_same_output bfTable bfTable r bfSchedule₁
    canonicalFixture.val hs rankFixture_success, hs⟩

-- 全射性の補題は隣接重複のある成功出力にも適用できる。
example : ∀ a : Fin 2, a ∈ ([0, 0, 1] : List (Fin 2)) := by
  let r : Schedule 2 1 := ⟨![1, 2], by decide⟩
  apply output_covers (fun _ => (1 : Equiv.Perm (Fin 2))) r
  decide

private lemma innerIdentityInverseRow :
    List.ofFn (1 : Equiv.Perm (Fin 2)).symm = [0, 1] := by decide
-- 内側射影が空の先頭・末尾行と、全消費する中間行を同時に融合する。
private def innerHorizontalEntries : List (Equiv.Perm (Fin 3) × ℕ) :=
  [(1, 1), (Equiv.swap 0 1, 3), (Equiv.swap 0 2, 2)]
private lemma innerHorizontalPrefix : ExtractionPrefix
    (fixedInnerRows (1 : Equiv.Perm (Fin 2)) 1 innerHorizontalEntries) []
    [[0], [1, 2, 0], [3, 0]] [1, 2, 3] := by
  have he : fixedInnerRows (1 : Equiv.Perm (Fin 2)) 1 innerHorizontalEntries =
      [([0, 1, 2, 3], 1), ([1, 2, 0, 3], 3), ([3, 1, 2, 0], 2)] := by decide
  rw [he]
  exact .cons (by decide) (by decide) (.cons (by decide) (by decide)
    (.cons (by decide) (by decide) (.nil _)))
example : ∃ r : ℕ, reduceRows [([0, 1], r)] ([] : List (Fin 2)) = some [0, 1] := by
  obtain ⟨r, hr⟩ := horizontal_inner_success (1 : Equiv.Perm (Fin 2)) 1
    innerHorizontalEntries [] [1, 2, 3] [[0], [1, 2, 0], [3, 0]] innerHorizontalPrefix
    (by decide)
  rw [innerIdentityInverseRow, List.filterMap_nil] at hr
  exact ⟨r, by convert hr using 1; decide⟩
-- 元の末尾が外側でも、復元した内側末尾一文字は共有端点として残す。
example : ∃ r : ℕ, ExtractionPrefix [([0, 1], r)] ([] : List (Fin 2)) [[0, 1]] [0] := by
  obtain ⟨r, hr⟩ := horizontal_inner_close (1 : Equiv.Perm (Fin 2)) (m := 2) 1
    [] 1 4 [] [] [] (.nil _) (by decide)
  rw [innerIdentityInverseRow] at hr
  exact ⟨r, by convert hr using 1 <;> decide⟩
-- 水平一歩の後の垂直移動から、内側非空性と末尾保持を追加仮定なしで得る。
example : ∃ r : ℕ, ExtractionPrefix [([0, 1], r)] ([] : List (Fin 2)) [[0]] [] := by
  have hp : ExtractionPrefix (fixedInnerRows (1 : Equiv.Perm (Fin 2)) (m := 2) 1 [(1, 1)])
      [] [[0]] [] := by
    have he : fixedInnerRows (1 : Equiv.Perm (Fin 2)) (m := 2) 1 [(1, 1)] =
        [([0, 1, 2, 3], 1)] := by decide
    rw [he]
    exact .cons (by decide) (by decide) (.nil _)
  have ht : reduceRows
      [(List.ofFn (BarrattEccles.permutationComposition 2 2 1 (Equiv.swap 0 1) 1).symm, 1),
        (List.ofFn (BarrattEccles.permutationComposition 2 2 1 (Equiv.swap 0 1)
          (Equiv.swap 0 1)).symm, 4)] [] = some [1, 2, 1, 0, 3] := by decide
  obtain ⟨r, hr⟩ := horizontal_inner_before_vertical (1 : Equiv.Perm (Fin 2))
    (Equiv.swap 0 1) (m := 2) 1 [(1, 1)] (Equiv.swap 0 1) 1 4 [] [] _ [[0]] [] hp ht
    (by decide)
  rw [innerIdentityInverseRow] at hr
  exact ⟨r, by convert hr using 1 <;> decide⟩
-- 水平零歩も同じ規則に含み、次の垂直移動の前の実際の除外状態を保持する。
example : ∃ r : ℕ, ExtractionPrefix [([0, 1], r)] ([] : List (Fin 2)) [[0]] [] := by
  have ht : reduceRows
      [(List.ofFn (BarrattEccles.permutationComposition 2 2 1 1 1).symm, 2),
        (List.ofFn (BarrattEccles.permutationComposition 2 2 1 1 (Equiv.swap 0 1)).symm, 3)] [] =
      some [0, 1, 2, 1, 3] := by decide
  obtain ⟨r, hr⟩ := horizontal_inner_before_vertical (1 : Equiv.Perm (Fin 2))
    (Equiv.swap 0 1) (m := 2) 1 [] 1 2 3 [] [] _ [] [] (.nil _) ht (by decide)
  rw [innerIdentityInverseRow] at hr
  exact ⟨r, by convert hr using 1 <;> decide⟩

-- 実際の軸方向条件から全水平区間を分割し、元の内側置換列へ戻す。
example : CompositeRecovery.InnerRunDecomposition gridRecoveryEntries
    [1, Equiv.swap 0 1] := by
  obtain ⟨sources, hd⟩ := CompositeRecovery.innerRunDecomposition_exists
    (1 : Equiv.Perm (Fin 4)) (1 : Equiv.Perm (Fin 2)) 2 gridRecoveryEntries.tail (by decide)
  have hm := hd.sources_eq
  have he : (1 : Equiv.Perm (Fin 2)) :: sources = [1, Equiv.swap 0 1] :=
    hm.symm.trans (by decide)
  rw [he] at hd
  exact hd
-- 水平・垂直が交互に現れる合成成功から、元の全内側行列の成功を得る。
example : ∃ table : List (List (Fin 2) × ℕ),
    reduceRows table [] = some [0, 1, 0] ∧
      table.map Prod.fst = List.ofFn (fun j => List.ofFn (terminalTable j).symm) ∧
      table.length = 2 := by
  have hentries : CompositeRecovery.shuffleTableEntries gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule = gridRecoveryEntries := by decide
  have hs : reduceRows (rows (fun i => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal i)) (terminalTable (gridRecoveryPath.vertical i)))
      gridRecoverySchedule) [] = some [0, 1, 2, 4, 2, 1, 4, 3] := by
    rw [← CompositeRecovery.shuffleTableEntries_rows 1 gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule, hentries]
    simpa using gridRecoveryPrefix.append [] [] rfl
  obtain ⟨table, ht, _, hm, hl, _⟩ := CompositeRecovery.shuffle_inner_recovery_with_rows
    (by decide) 1 gridRecoveryPath bfTable terminalTable gridRecoverySchedule _ hs (by decide)
  refine ⟨table, ?_, hm, hl⟩
  have hw : CompositeRecovery.innerWord (m := 3) (n := 2) 1
      [0, 1, 2, 4, 2, 1, 4, 3] = [0, 1, 0] := by decide
  rwa [hw] at ht
-- 内側次数零では、内側射影が空の最終行も全表に含めて元の一行を得る。
example : ∃ table : List (List (Fin 2) × ℕ),
    reduceRows table [] = some [0, 1] ∧ table.map Prod.fst = [[0, 1]] := by
  let entries : List (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2) × ℕ) :=
    innerHorizontalEntries.map (fun p => (p.1, 1, p.2))
  have hs : reduceRows (CompositeRecovery.mixedTable 1 entries) [] =
      some [0, 1, 2, 0, 3, 0] := by
    rw [CompositeRecovery.mixedTable_horizontal]
    simpa using innerHorizontalPrefix.append [] [] rfl
  obtain ⟨table, hm, ht⟩ := CompositeRecovery.inner_table_success 1 entries [] _ hs
    (by decide) (by decide) (by decide)
  refine ⟨table, ?_, ?_⟩
  · have hw : CompositeRecovery.innerWord (m := 2) (n := 2) 1
        [0, 1, 2, 0, 3, 0] = [0, 1] := by decide
    simpa only [List.filterMap_nil, hw] using ht
  · exact hm.trans (by decide)

private lemma innerGrid_success : reduceRows (rows (fun i =>
    BarrattEccles.permutationComposition 3 2 1 (bfTable (gridRecoveryPath.horizontal i))
      (terminalTable (gridRecoveryPath.vertical i))) gridRecoverySchedule) [] =
    some [0, 1, 2, 4, 2, 1, 4, 3] := by
  have he : CompositeRecovery.shuffleTableEntries gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule = gridRecoveryEntries := by decide
  rw [← CompositeRecovery.shuffleTableEntries_rows 1 gridRecoveryPath bfTable terminalTable
    gridRecoverySchedule, he]
  simpa using gridRecoveryPrefix.append [] [] rfl
private lemma innerGrid_word : CompositeRecovery.innerWord (m := 3) (n := 2) 1
    [0, 1, 2, 4, 2, 1, 4, 3] = List.ofFn compositionInner.val := by decide
-- 行長総和を仮定せず復元した内側 Schedule が既知の元の Schedule に一致する。
example : ∃ r : Schedule 2 1, r = terminalSchedule ∧
    reduceRows (rows terminalTable r) [] = some (List.ofFn compositionInner.val) := by
  obtain ⟨r, hs, _, _⟩ := CompositeRecovery.shuffle_inner_schedule (by decide) 1 gridRecoveryPath
    bfTable terminalTable gridRecoverySchedule _ innerGrid_success (by decide)
  rw [innerGrid_word] at hs
  exact ⟨r, schedule_eq_of_same_output terminalTable terminalTable r terminalSchedule
    compositionInner.val hs verticalInner_success, hs⟩
-- 内側基底語の元の次数と成功 Schedule の一意性も実際の shuffle 成功から得る。
example : ∃ v : BasisWord 2 1, v = compositionInner ∧
    ∃! r : Schedule 2 1, reduceRows (rows terminalTable r) [] = some (List.ofFn v.val) := by
  obtain ⟨v, hv, hr⟩ := CompositeRecovery.shuffle_inner_basis (by decide) 1 gridRecoveryPath
    bfTable terminalTable gridRecoverySchedule _ innerGrid_success (by decide)
  refine ⟨v, ?_, hr⟩
  apply Subtype.ext
  exact List.ofFn_injective (hv.trans innerGrid_word)
-- 内側次数零でも、内側を選ばない末尾行を含む全合成 Schedule から復元する。
example : ∃ r : Schedule 2 0,
    reduceRows (rows (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 2))) r) [] = some [0, 1] := by
  let s : BarrattEccles.ShufflePath 2 0 := ⟨{0, 1}, by decide⟩
  let outer : Fin 3 → Equiv.Perm (Fin 3) := ![1, Equiv.swap 0 1, Equiv.swap 0 2]
  let inner : Fin 1 → Equiv.Perm (Fin 2) := fun _ => 1
  let r : Schedule 4 2 := ⟨![1, 3, 2], by decide⟩
  have hs : reduceRows (rows (fun i => BarrattEccles.permutationComposition 2 2 1
      (outer (s.horizontal i)) (inner (s.vertical i))) r) [] =
      some [0, 1, 2, 0, 3, 0] := by decide
  obtain ⟨q, hq, _, _⟩ := CompositeRecovery.shuffle_inner_schedule (by decide) 1 s outer inner r
    _ hs (by decide)
  have hw : CompositeRecovery.innerWord (m := 2) (n := 2) 1 [0, 1, 2, 0, 3, 0] = [0, 1] := by decide
  exact ⟨q, by simpa only [hw] using hq⟩

-- 隣接重複だけの縮約損失を数え、離れた同値を含む部分語の全共有端点を導く。
example : ([[0, 1, 0], [0, 2], [2, 0]] : List (List (Fin 3))).IsChain
    (fun pre post => pre.getLast? = post.head?) := by
  exact AdjacentCollapse.shared_endpoints_of_saturated _ (by decide) (by decide) (by decide)
-- 同じ三部分語から既存の OverlapPartition の全 segment を実際に再構成する。
example : ∃! r : OverlapPartition 3 5,
    r.segments (![0, 1, 0, 2, 0] : Fin 5 → Fin 3) = [[0, 1, 0], [0, 2], [2, 0]] := by
  exact OverlapPartition.existsUnique_of_rows
    ([[0, 1, 0], [0, 2], [2, 0]] : List (List (Fin 3))) (by decide) (by decide)
    (![0, 1, 0, 2, 0] : Fin 5 → Fin 3) (by decide) (by decide)
-- 実際の交互 shuffle 出力から取り出した区間が、元の既知の分割を一意に復元する。
private def gridSplitParts : List (List (Fin 2)) :=
  CompositeRecovery.splitParts 1 (List.ofFn canonicalFixture.val) [0, 1, 2, 4, 2, 1, 4, 3]
private lemma gridSplitParts_value : gridSplitParts = [[0, 1], [1, 0]] := by decide
example : ∃ r : OverlapPartition 2 3, r = verticalCuts ∧
    r.segments compositionInner.val = gridSplitParts := by
  have hc : ∀ row ∈ gridSplitParts, row.IsChain (· ≠ ·) := by
    rw [gridSplitParts_value]
    decide
  have hn : ∀ row ∈ gridSplitParts, row ≠ [] := by rw [gridSplitParts_value]; decide
  have hv : List.ofFn compositionInner.val = AdjacentCollapse.collapse gridSplitParts.flatten :=
    by decide
  have hs : gridSplitParts.flatten.length + 1 = 3 + gridSplitParts.length := by decide
  have hp := OverlapPartition.existsUnique_of_rows gridSplitParts hc hn compositionInner.val hv hs
  have hl : gridSplitParts.length = 2 := by decide
  rw [hl] at hp
  obtain ⟨r, hr, hu⟩ := hp
  have hknown : verticalCuts.segments compositionInner.val = gridSplitParts := by decide
  exact ⟨r, (hu verticalCuts hknown).symm, hr⟩
-- 異なる境界の二語は一文字も失わず、飽和条件の必要性を検証する。
example : (AdjacentCollapse.collapse ([0, 1] ++ [2, 0] : List (Fin 3))).length = 4 := by
  have h := AdjacentCollapse.collapse_append_length ([0, 1] : List (Fin 3)) [2, 0]
    (by decide) (by decide) (by decide) (by decide)
  simpa using h

-- 共有端点を入力せず、一般の代入分解と復元両語長から実際の分割を一意に構成する。
example : ∃ p : OverlapPartition 2 3, p = verticalCuts ∧
    compositeWord canonicalFixture compositionInner 1 p = [0, 1, 2, 4, 2, 1, 4, 3] := by
  have ho : List.ofFn canonicalFixture.val = CompositeRecovery.outerWord (m := 3) (n := 2) 1
      [0, 1, 2, 4, 2, 1, 4, 3] := by decide
  obtain ⟨p, hp, hu⟩ := CompositeRecovery.recovered_partition_existsUnique canonicalFixture
    compositionInner 1 [0, 1, 2, 4, 2, 1, 4, 3] (by decide) (by decide) ho innerGrid_word.symm
  have hk : compositeWord canonicalFixture compositionInner 1 verticalCuts =
      [0, 1, 2, 4, 2, 1, 4, 3] := by decide
  exact ⟨p, (hu verticalCuts hk).symm, hp⟩
-- 実際の成功から元の両語・一意な分割・一意な両成功 Schedule を全て得る。
example : ∃ u : BasisWord 4 2, ∃ v : BasisWord 2 1,
    u = canonicalFixture ∧ v = compositionInner ∧
      (∃! p : OverlapPartition (occurrenceCount u.val 1) 3,
        compositeWord u v 1 p = [0, 1, 2, 4, 2, 1, 4, 3]) ∧
      (∃! su : Schedule 4 2, reduceRows (rows bfTable su) [] = some (List.ofFn u.val)) ∧
      (∃! sv : Schedule 2 1, reduceRows (rows terminalTable sv) [] = some (List.ofFn v.val)) := by
  obtain ⟨u, v, hp, hu, hv, hsu, hsv⟩ := CompositeRecovery.shuffle_source_partition (by decide) 1
    gridRecoveryPath bfTable terminalTable gridRecoverySchedule _ innerGrid_success (by decide)
  have ho : CompositeRecovery.outerWord (m := 3) (n := 2) 1 [0, 1, 2, 4, 2, 1, 4, 3] =
      List.ofFn canonicalFixture.val := by decide
  refine ⟨u, v, ?_, ?_, hp, hsu, hsv⟩
  · exact Subtype.ext (List.ofFn_injective (hu.trans ho))
  · exact Subtype.ext (List.ofFn_injective (hv.trans innerGrid_word))
-- 部分語分解自体は内側 arity 零にも適用でき、指定値のない復元外側語へ戻る。
example : ([0, 1] : List (Fin 2)) = substitute (n := 0) 1 [0, 2] [] := by
  have hp := CompositeRecovery.splitParts_properties (m := 2) (n := 0) 1 [0, 1] (by decide)
  have ho : CompositeRecovery.outerWord (m := 2) (n := 0) 1 [0, 1] = [0, 2] := by decide
  rw [ho] at hp
  have hs : CompositeRecovery.splitParts (m := 2) (n := 0) 1 [0, 2] [0, 1] = [] := by decide
  rw [hs] at hp
  exact hp.2.2.2

-- 実際の選択行列の三境界から、垂直一歩・水平二歩を元の経路なしで検出する。
example : ∀ i : Fin 3, CompositeRecovery.BoundaryInserted (m := 3) (n := 2) 1
    [[0, 1], [2], [4], [2, 1, 4, 3]] i.val ↔ i = 0 := by
  have ht : ExtractionTrace (rows (fun j => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal j)) (terminalTable (gridRecoveryPath.vertical j)))
      gridRecoverySchedule) [] [[0, 1], [2], [4], [2, 1, 4, 3]] := by
    apply extractionTrace_of_lengths
    · simpa using innerGrid_success
    · decide
  intro i
  exact (CompositeRecovery.boundaryInserted_iff_notMem 1 gridRecoveryPath bfTable terminalTable
    gridRecoverySchedule _ ht (by decide) i).trans (by fin_cases i <;> decide)
-- 一般の経路一意性から、正方向で構成した経路が元の実際の経路へ戻る。
private lemma gridPath_roundtrip :
    compositionPath canonicalFixture compositionInner 1 verticalCuts = gridRecoveryPath := by
  exact fullCompositionFixture.compositionPath_eq_of_success gridRecoveryPath gridRecoverySchedule
    _ innerGrid_success (by decide) (by decide)
private lemma gridSchedule_roundtrip : fullCompositionFixture.fusedSchedule =
    gridRecoverySchedule := by
  exact fullCompositionFixture.fusedSchedule_eq_of_success gridRecoveryPath gridRecoverySchedule
    _ innerGrid_success (by decide)
-- 元の成功二表・分割・経路・Schedule を全て戻す入力データが一意に構成される。
example : ∃ c : TableCompositionData 3 2 2 1, c = fullCompositionFixture ∧
    compositionPath c.outerWord c.innerWord c.slot c.cuts = gridRecoveryPath ∧
      c.fusedSchedule = gridRecoverySchedule := by
  obtain ⟨c, hc, hu⟩ := CompositeRecovery.shuffle_reconstruction_existsUnique (by decide) 1
    gridRecoveryPath bfTable terminalTable gridRecoverySchedule _ innerGrid_success (by decide)
  have hk : fullCompositionFixture.outer = bfTable ∧ fullCompositionFixture.inner = terminalTable ∧
      fullCompositionFixture.slot = 1 ∧ compositionPath fullCompositionFixture.outerWord
        fullCompositionFixture.innerWord fullCompositionFixture.slot fullCompositionFixture.cuts =
          gridRecoveryPath ∧ fullCompositionFixture.fusedSchedule = gridRecoverySchedule ∧
      compositeWord fullCompositionFixture.outerWord fullCompositionFixture.innerWord
        fullCompositionFixture.slot fullCompositionFixture.cuts = [0, 1, 2, 4, 2, 1, 4, 3] :=
    ⟨rfl, rfl, rfl, gridPath_roundtrip, gridSchedule_roundtrip, by decide⟩
  exact ⟨c, (hu fullCompositionFixture hk).symm, hc.2.2.2.1, hc.2.2.2.2.1⟩

private def fullSuccessSource : CompositionSuccess.Source bfTable terminalTable (1 : Fin 4) :=
  ⟨fullCompositionFixture, rfl, rfl, rfl⟩
private def gridSuccessTarget : CompositionSuccess.Target bfTable terminalTable (1 : Fin 4) :=
  ⟨(gridRecoveryPath, gridRecoverySchedule), _, innerGrid_success, by decide⟩
-- 有限成功項全単射の正方向は実際の既知の混合経路・Schedule を返す。
private lemma successForward_grid : CompositionSuccess.forward (by decide) fullSuccessSource =
    gridSuccessTarget := by
  apply Subtype.ext
  exact Prod.ext gridPath_roundtrip gridSchedule_roundtrip
-- 選んだ逆写像も元の成功二表と分割へ厳密に戻る。
example : (CompositionSuccess.equiv (by decide) bfTable terminalTable (1 : Fin 4)).symm
    gridSuccessTarget = fullSuccessSource := by
  have he : (CompositionSuccess.equiv (by decide) bfTable terminalTable (1 : Fin 4))
      fullSuccessSource = gridSuccessTarget := successForward_grid
  have hh := congrArg (CompositionSuccess.equiv (by decide) bfTable terminalTable (1 : Fin 4)).symm he
  simpa only [Equiv.symm_apply_apply] using hh.symm
-- 正方向の項の一致には経路の符号も含む。
example : CompositionSuccess.signedTerm ℤ bfTable terminalTable (1 : Fin 4)
    gridSuccessTarget.val = CompositionSuccess.sourceTerm ℤ fullSuccessSource := by
  rw [← successForward_grid]
  exact CompositionSuccess.forward_term ℤ (by decide) fullSuccessSource
-- 退化出力となる別の実際の Schedule は全経路和に含めても零。
private def degenerateGridSchedule : Schedule 5 3 := ⟨![5, 1, 1, 1], by decide⟩
example : CompositionSuccess.signedTerm ℤ bfTable terminalTable (1 : Fin 4)
    (gridRecoveryPath, degenerateGridSchedule) = 0 := by
  apply CompositionSuccess.signedTerm_eq_zero_of_not_successful
  rintro ⟨out, ho, hc⟩
  have hz : reduceRows (rows (fun j => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal j)) (terminalTable (gridRecoveryPath.vertical j)))
      degenerateGridSchedule) [] = some [0, 1, 2, 3, 4, 4, 4, 4] := by decide
  have he : out = [0, 1, 2, 3, 4, 4, 4, 4] := Option.some.inj (ho.symm.trans hz)
  rw [he] at hc
  exact (by decide : ¬ ([0, 1, 2, 3, 4, 4, 4, 4] : List (Fin 5)).IsChain (· ≠ ·)) hc
-- 全経路・全 Schedule を含む和が元の全成功二表と分割の符号付き和に一致する。
example :
    letI := CompositionSuccess.sourceFintype (by decide) bfTable terminalTable (1 : Fin 4)
    (∑ s : BarrattEccles.ShufflePath 2 1, (s.sign : ℤ) • onSequence ℤ (fun j =>
      BarrattEccles.permutationComposition 3 2 1 (bfTable (s.horizontal j))
        (terminalTable (s.vertical j)))) =
      ∑ c : CompositionSuccess.Source bfTable terminalTable (1 : Fin 4),
        CompositionSuccess.sourceTerm ℤ c :=
  CompositionSuccess.sum_onSequence_eq_source ℤ (by decide) bfTable terminalTable 1

private def outerSuccessfulWord : SuccessfulWord bfTable :=
  ⟨(bfSchedule₁, canonicalFixture), rankFixture_success⟩
private def innerSuccessfulWord : SuccessfulWord terminalTable :=
  ⟨(terminalSchedule, compositionInner), verticalInner_success⟩
-- 元の入力データを二列の実際の成功と分割へ、添字の移送を含めて分ける。
example : (CompositionSuccess.wordsEquiv (by decide) bfTable terminalTable (1 : Fin 4))
    fullSuccessSource = ⟨outerSuccessfulWord, innerSuccessfulWord, verticalCuts⟩ := rfl
-- 各元列の TR を、実際の成功基底語の有限和へ展開する。
example : onSequence ℤ bfTable =
    ∑ p : SuccessfulWord bfTable, basis ℤ 4 2 (ULift.up p.val.2) :=
  onSequence_eq_sum_successfulWords ℤ (by decide) bfTable
-- 混合する全 shuffle と全 Schedule の和が、元の二つの TR の実際の部分合成に一致する。
example :
    (∑ s : BarrattEccles.ShufflePath 2 1, (s.sign : ℤ) • onSequence ℤ (fun j =>
      BarrattEccles.permutationComposition 3 2 1 (bfTable (s.horizontal j))
        (terminalTable (s.vertical j)))) =
      Surjection.partialComposition ℤ 3 2 2 1 1 (onSequence ℤ bfTable)
        (onSequence ℤ terminalTable) :=
  onSequence_partialComposition_of_pos ℤ (by decide) bfTable terminalTable 1
-- 一方の元列が退化している場合も一般公式に含まれ、全 shuffle 側が零へ戻る。
example :
    (∑ s : BarrattEccles.ShufflePath 1 0, (s.sign : ℤ) • onSequence ℤ (fun j =>
      BarrattEccles.permutationComposition 1 2 0
        ((fun _ : Fin 2 => (1 : Equiv.Perm (Fin 2))) (s.horizontal j))
        ((fun _ : Fin 1 => (1 : Equiv.Perm (Fin 2))) (s.vertical j)))) = 0 := by
  let outer : Fin 2 → Equiv.Perm (Fin 2) := fun _ => 1
  let inner : Fin 1 → Equiv.Perm (Fin 2) := fun _ => 1
  have h := onSequence_partialComposition_of_pos ℤ (by decide) outer inner (0 : Fin 2)
  have ho : onSequence ℤ outer = 0 :=
    onSequence_eq_zero_of_adjacent_eq ℤ outer 0 1 (by decide) rfl
  rw [ho] at h
  simpa only [map_zero, LinearMap.zero_apply] using h

-- 生成元上の有限和の一致を、実際の正規化鎖の任意の元の双線形合成まで延長する。
example (x : (BarrattEccles.normalizedChains ℤ 4).X 2)
    (y : (BarrattEccles.normalizedChains ℤ 2).X 1) :
    normalizedMap ℤ 5 3 (BarrattEccles.shuffleBilinear ℤ 3 2 1 2 1 x y) =
      Surjection.partialComposition ℤ 3 2 2 1 1 (normalizedMap ℤ 4 2 x)
        (normalizedMap ℤ 2 1 y) :=
  normalizedMap_shuffleBilinear_of_pos ℤ (by decide) 1 x y

-- 零 arity の正の内側次数でも、全正規化鎖に対する合成保存が成立する。
example (x : (BarrattEccles.normalizedChains ℤ 4).X 2)
    (y : (BarrattEccles.normalizedChains ℤ 0).X 1) :
    normalizedMap ℤ 3 3 (BarrattEccles.shuffleBilinear ℤ 3 0 1 2 1 x y) =
      Surjection.partialComposition ℤ 3 0 2 1 1 (normalizedMap ℤ 4 2 x)
        (normalizedMap ℤ 0 1 y) :=
  normalizedMap_shuffleBilinear_nullary_succ ℤ 1 x y
-- 外側出力 arity も零になる境界を含め、実際の各 shuffle 項が零となる。
example (s : BarrattEccles.ShufflePath 2 1)
    (outer : Fin 3 → Equiv.Perm (Fin 1)) (inner : Fin 2 → Equiv.Perm (Fin 0)) :
    onSequence ℤ (fun j => BarrattEccles.permutationComposition 0 0 0
      (outer (s.horizontal j)) (inner (s.vertical j))) = 0 :=
  onSequence_shuffle_nullary_succ ℤ 0 2 0 0 outer inner s
-- 空語挿入は一出現だけを残し、二出現の場合は分割が存在せず零になる。
private def emptyNullaryWord : BasisWord 0 0 := permutationWord 1
example : eraseSlotWord (0 : Fin 4) (List.ofFn canonicalFixture.val) = [0, 2, 0, 2, 1] := by
  decide
example : compositionOnWords ℤ canonicalFixture emptyNullaryWord 0 =
    listGenerator ℤ (d := 2) [0, 2, 0, 2, 1] := by
  rw [compositionOnWords_nullary_of_count_eq_one ℤ _ _ _ (by decide)]
  rfl
example : compositionOnWords ℤ canonicalFixture emptyNullaryWord 1 = 0 :=
  compositionOnWords_nullary_of_count_ne_one ℤ _ _ _ (by decide)
-- 反転した実際の置換行でも、指定値削除は既存 BE の空語挿入に一致する。
example : List.ofFn
    (BarrattEccles.permutationComposition 2 0 1 rowOuter (1 : Equiv.Perm (Fin 0))).symm =
      [1, 0] := by
  rw [permutationComposition_inverse_row_nullary]
  decide
-- 早期除外した元の二行の成功と削除後の成功を、全抽出の公式で結ぶ。
example :
    reduceRows [([0, 1], 1), ([0, 1], 2)] ([] : List (Fin 2)) =
      (reduceRows [([0, 1, 2], 1), ([0, 1, 2], 2)] [0]).map
        (eraseSlotWord (0 : Fin 3)) := by
  have h := reduceRows_eraseSlotWord_of_mem (0 : Fin 3)
    [([0, 1, 2], 1), ([0, 1, 2], 2)] [0] (by decide)
  exact h
example : reduceRows [([0, 1], 1), ([0, 1], 2)] ([] : List (Fin 2)) =
    some [0, 0, 1] := by decide

-- 非退化の nullary 成功表から、一回だけ指定値を挿入する実際の逆構成。
private def nullaryOuter : Fin 2 → Equiv.Perm (Fin 3) := ![1, Equiv.swap 1 2]
example : reduceRows (rows (fun j => BarrattEccles.permutationComposition 2 0 0
    (nullaryOuter j) (1 : Equiv.Perm (Fin 0))) terminalSchedule) [] = some [0, 1, 0] := by
  decide
example : reduceRows (nullarySourceRows nullaryOuter terminalSchedule) [0] =
    some [1, 2, 1] := by decide
example : ∃ before chosen after pre post,
    nullarySourceRows nullaryOuter terminalSchedule = before ++ chosen :: after ∧
    (0 : Fin 3) ∉ pre ∧ 0 ∉ post ∧ [0, 1, 0] = eraseSlotWord 0 (pre ++ post) ∧
    reduceRows (before ++ (chosen.1, chosen.2 + 1) :: after) [] =
      some (pre ++ 0 :: post) :=
  nullary_success_extension nullaryOuter 1 0 terminalSchedule [0, 1, 0] (by decide)

-- 延長された行長は元の Schedule であり、削除後の非退化語へ戻る。
private def nullaryLiftSchedule : Schedule 3 1 := ⟨![2, 2], by decide⟩
private def nullaryLiftWord : BasisWord 3 1 := ⟨![0, 1, 2, 1], by decide⟩
private def nullaryLiftSuccess : SuccessfulWord nullaryOuter :=
  ⟨(nullaryLiftSchedule, nullaryLiftWord), by decide⟩
private def nullaryLiftSource : NullarySource nullaryOuter 0 :=
  ⟨nullaryLiftSuccess, by decide⟩
private def nullaryTargetSuccess : SuccessfulWord (fun j =>
    BarrattEccles.permutationComposition 2 0 0 (nullaryOuter j) 1) :=
  ⟨(terminalSchedule, compositionInner), by decide⟩
example : List.ofFn (nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource).val.2.val =
    [0, 1, 0] := by
  rw [nullaryForward_word]
  rfl
example : nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource =
    nullaryTargetSuccess := by
  apply successfulWord_eq_of_word_eq _ _ _
  rw [nullaryForward_word]
  rfl
-- 空語との部分合成が実際の目標基底元へ一致することも係数環 ℤ 上で検証。
example : compositionOnWords ℤ nullaryLiftWord emptyNullaryWord 0 =
    basis ℤ 2 1 (ULift.up compositionInner) := by
  have h := nullaryForward_term ℤ (by decide) nullaryOuter 1 0 nullaryLiftSource
  rw [show nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource =
    nullaryTargetSuccess by
      apply successfulWord_eq_of_word_eq _ _ _
      rw [nullaryForward_word]
      rfl] at h
  exact h
-- 各実際の成功基底語には、語の削除で元へ戻る一出現の成功基底語が存在する。
example : ∃ p : SuccessfulWord nullaryOuter, occurrenceCount p.val.2.val 0 = 1 ∧
    eraseSlotWord 0 (List.ofFn p.val.2.val) = [0, 1, 0] :=
  nullary_successfulWord_lift_exists nullaryOuter 1 0 nullaryTargetSuccess
example : Function.Surjective (nullaryForward (by decide) nullaryOuter 1 (0 : Fin 3)) :=
  nullaryForward_surjective (by decide) nullaryOuter 1 0

-- 空語合成の有限対応は全単射で、具体的な非自明な二行の成功項を往復する。
example : nullarySuccessEquiv (by decide) nullaryOuter 1 0 nullaryLiftSource =
    nullaryTargetSuccess := by
  change nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource = nullaryTargetSuccess
  apply successfulWord_eq_of_word_eq _ _ _
  rw [nullaryForward_word]
  rfl
example : (nullarySuccessEquiv (by decide) nullaryOuter 1 0).symm nullaryTargetSuccess =
    nullaryLiftSource := by
  apply (nullarySuccessEquiv (by decide) nullaryOuter 1 0).injective
  rw [Equiv.apply_symm_apply]
  symm
  change nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource = nullaryTargetSuccess
  apply successfulWord_eq_of_word_eq _ _ _
  rw [nullaryForward_word]
  rfl
-- 元の全成功項の空語部分合成和が、実際の削除表の TR に一致する。
example : onSequence ℤ (fun j => BarrattEccles.permutationComposition 2 0 0
    (nullaryOuter j) (1 : Equiv.Perm (Fin 0))) =
      Surjection.partialComposition ℤ 2 0 1 0 0 (onSequence ℤ nullaryOuter)
        (basis ℤ 0 0 (ULift.up emptyNullaryWord)) :=
  onSequence_nullary_composition_of_pos ℤ (by decide) nullaryOuter 1 0
-- 出力 arity 零・次数零の明示的な空語境界も一般公式に含まれる。
example : onSequence ℤ (fun j : Fin 1 => BarrattEccles.permutationComposition 0 0 0
    ((fun _ : Fin 1 => (1 : Equiv.Perm (Fin 1))) j) (1 : Equiv.Perm (Fin 0))) =
      Surjection.partialComposition ℤ 0 0 0 0 0
        (onSequence ℤ (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 1))))
        (basis ℤ 0 0 (ULift.up emptyNullaryWord)) :=
  onSequence_nullary_composition_zero_output ℤ 0
    (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 1))) 1 0
-- 内側零次数の全 shuffle 和に、退化する元列も含める。
example :
    (∑ s : BarrattEccles.ShufflePath 2 0, (s.sign : ℤ) • onSequence ℤ (fun j =>
      BarrattEccles.permutationComposition 3 0 1 (bfTable (s.horizontal j))
        ((fun _ : Fin 1 => (1 : Equiv.Perm (Fin 0))) (s.vertical j)))) =
      Surjection.partialComposition ℤ 3 0 2 0 1 (onSequence ℤ bfTable)
        (onSequence ℤ (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 0)))) :=
  onSequence_partialComposition ℤ 1 bfTable
    (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 0)))
-- 任意の可換環・全 arity・全次数で、実際の正規化鎖の双線形合成を保存する。
example (A : Type) [CommRing A] (m n d e : ℕ) (k : Fin (m + 1))
    (x : (BarrattEccles.normalizedChains A (m + 1)).X d)
    (y : (BarrattEccles.normalizedChains A n).X e) :
    normalizedMap A (m + n) (d + e) (BarrattEccles.shuffleBilinear A m n k d e x y) =
      Surjection.partialComposition A m n d e k (normalizedMap A (m + 1) d x)
        (normalizedMap A n e y) := normalizedMap_shuffleBilinear A k x y
example (x : (BarrattEccles.normalizedChains ℤ 1).X 2)
    (y : (BarrattEccles.normalizedChains ℤ 0).X 0) :
    normalizedMap ℤ 0 2 (BarrattEccles.shuffleBilinear ℤ 0 0 0 2 0 x y) =
      Surjection.partialComposition ℤ 0 0 2 0 0 (normalizedMap ℤ 1 2 x)
        (normalizedMap ℤ 0 0 y) := normalizedMap_shuffleBilinear ℤ 0 x y

-- 全射語の二つの正次数の合成の微分には、外側が奇次数の場合に負符号が付く。
example (x : degreeModule ℤ 3 1) (y : degreeModule ℤ 2 1) :
    differential ℤ 4 1 (Surjection.partialComposition ℤ 2 2 1 1 0 x y) =
      Surjection.partialComposition ℤ 2 2 0 1 0 (differential ℤ 3 0 x) y -
        Surjection.partialComposition ℤ 2 2 1 0 0 x (differential ℤ 2 0 y) := by
  have h := Surjection.partialComposition_d_positive ℤ 2 2 0 0 0 x y
  rw [show (-1 : ℤ) ^ (0 + 1) = -1 by decide, neg_one_zsmul] at h
  simpa only [Surjection.degreeTransport_refl, sub_eq_add_neg] using h
-- 空語挿入の場合も外側微分との可換性を保つ。
example (x : degreeModule ℤ 3 2) :
    differential ℤ 2 1 (Surjection.partialComposition ℤ 2 0 2 0 1 x
      (basis ℤ 0 0 (ULift.up emptyNullaryWord))) =
      Surjection.partialComposition ℤ 2 0 1 0 1 (differential ℤ 3 1 x)
        (basis ℤ 0 0 (ULift.up emptyNullaryWord)) :=
  Surjection.partialComposition_d_rightZero ℤ 2 0 1 1 x _
-- 一文字単位と空語への左単位、正次数への右単位。
example : Surjection.unitElement ℤ = basis ℤ 1 0 (ULift.up (permutationWord 1)) := rfl
example : Surjection.degreeTransport ℤ 0 (Nat.zero_add 0)
    (Surjection.arityTransport ℤ (Nat.zero_add 0) 0
      (Surjection.partialComposition ℤ 0 0 0 0 0 (Surjection.unitElement ℤ)
        (basis ℤ 0 0 (ULift.up emptyNullaryWord)))) =
      basis ℤ 0 0 (ULift.up emptyNullaryWord) :=
  Surjection.partialComposition_left_unit ℤ 0 0 _
example : Surjection.partialComposition ℤ 2 1 1 0 2
    (basis ℤ 3 1 (ULift.up compositionOuter)) (Surjection.unitElement ℤ) =
      basis ℤ 3 1 (ULift.up compositionOuter) :=
  Surjection.partialComposition_right_unit ℤ 2 2 1 _
-- 交換する二つの内側演算がともに奇次数なら並列交換の符号は負。
example (x : degreeModule ℤ 3 1) (y z : degreeModule ℤ 2 1) :
    Surjection.partialComposition ℤ 3 2 2 1 (BarrattEccles.parallelSlot 1 2 0 2 (by decide))
      (Surjection.partialComposition ℤ 2 2 1 1 0 x y) z =
      -Surjection.partialComposition ℤ 3 2 2 1
        (BarrattEccles.parallelSlot 1 2 2 0 (by decide))
        (Surjection.partialComposition ℤ 2 2 1 1 2 x z) y := by
  have h := Surjection.partialComposition_parallel_assoc ℤ 1 2 2 0 2 (by decide) 1 1 1 x y z
  rw [show (-1 : ℤ) ^ (1 * 1) = -1 by decide, neg_one_zsmul] at h
  simpa only [Surjection.degreeTransport_refl, Surjection.arityTransport_refl] using h
-- 整数複体の対称列と、その全射 TR の成分を検証する。
example : SerrePositivity.SymmetricSequence.level (Surjection.sequence ℤ) 2 = Surjection.complex ℤ 2 := rfl
example : (TableReduction.sequenceMap ℤ).app (SerrePositivity.FiniteBijection.of 2) = cochainMap ℤ 2 := rfl
example : Function.Surjective ((cochainMap ℤ 2).f (-2)).hom := cochainMap_f_surjective ℤ 2 2

open CategoryTheory CategoryTheory.MonoidalCategory

-- 非自明な二つの負次数の純粋テンソルで、整数部分合成は元の全射語合成になる。
open SerrePositivity.DifferentialGraded HomologicalComplex in
example (x : (Surjection.complex ℤ 3).X (-1)) (y : (Surjection.complex ℤ 2).X (-1)) :
    (Surjection.complexPartialComposition ℤ 2 2 0).f (-2)
        (ιTensorObj (Surjection.complex ℤ 3) (Surjection.complex ℤ 2) (-1) (-1) (-2)
          (by decide) (x ⊗ₜ[ℤ] y)) =
      (Surjection.complexXIso ℤ 4 2).inv
        (Surjection.partialComposition ℤ 2 2 1 1 0
          ((Surjection.complexXIso ℤ 3 1).hom x) ((Surjection.complexXIso ℤ 2 1).hom y)) :=
  Surjection.complexPartialComposition_neg_tmul ℤ 2 2 0 1 1 x y
-- 空語を含む実際の整数複体の射の合成保存。
example : BarrattEccles.partialComposition ℤ 2 0 1 ≫ cochainMap ℤ 2 =
    (cochainMap ℤ 3 ⊗ₘ cochainMap ℤ 0) ≫ Surjection.complexPartialComposition ℤ 2 0 1 :=
  complexPartialComposition_comm ℤ 2 0 1
-- 正次数の零成分も含めて整数 TR の全射性とテンソル消去が使える。
example : Function.Surjective ((cochainMap ℤ 0).f 1).hom := cochainMap_f_surjective_int ℤ 0 1
example : Epi (cochainMap ℤ 2 ⊗ₘ cochainMap ℤ 0) := tensor_cochainMap_epi ℤ 2 0
-- 複体射の単位の保存と、全整数次数を同時に扱う右単位則。
example : BarrattEccles.unit ℤ ≫ cochainMap ℤ 1 = Surjection.complexUnit ℤ := rfl
example : (Surjection.complex ℤ 3 ◁ Surjection.complexUnit ℤ) ≫
    Surjection.complexPartialComposition ℤ 2 1 2 = (ρ_ (Surjection.complex ℤ 3)).hom :=
  Surjection.complexPartialComposition_right_unit ℤ 2 2
-- 内側の非自明な置換も複体射の段階で同変。
example : (Surjection.complex ℤ 3 ◁ Surjection.complexRename ℤ 2 (Equiv.swap 0 1)⁻¹) ≫
    Surjection.complexPartialComposition ℤ 2 2 0 =
      Surjection.complexPartialComposition ℤ 2 2 0 ≫
        Surjection.complexRename ℤ 4
          (operadInnerPermutation 2 2 0 (Equiv.swap 0 1))⁻¹ :=
  Surjection.complexPartialComposition_inner_rightAction ℤ 2 2 0 (Equiv.swap 0 1)

-- 束ねた TR オペラッド射は nullary の代入にも構成済みの合成保存を使う。
example : BarrattEccles.partialComposition ℤ 2 0 1 ≫
    (TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 2) =
      ((TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 3) ⊗ₘ
        (TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 0)) ≫
          (Surjection.operad ℤ).comp 2 0 1 :=
  (TableReduction.operadMap ℤ).comp 2 0 1
-- 出力 arity 零の負次数と正次数の零成分も、同じオペラッド射の全射性が扱う。
example : Function.Surjective
    (((TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 0)).f (-2)).hom :=
  TableReduction.operadMap_f_surjective ℤ 0 (-2)
example : Function.Surjective
    (((TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 0)).f 1).hom :=
  TableReduction.operadMap_f_surjective ℤ 0 1

open SerrePositivity.EInfinity.IntervalCuts

-- 010 の唯一の非退化な辺の切断は、正符号の辺⊗辺を与える。
example : edgeValue ℤ compositionInner =
    Finsupp.single (fun _ : Fin 2 => IntervalCuts.edge) 1 := by
  have h0 : ¬ EdgeNondegenerate compositionInner.val 0 := by decide
  have h1 : EdgeNondegenerate compositionInner.val 1 := by decide
  have h2 : ¬ EdgeNondegenerate compositionInner.val 2 := by decide
  have hs : edgeSign compositionInner.val 1 = 1 := by decide
  have ho : edgeOutput compositionInner 1 = (fun _ : Fin 2 => IntervalCuts.edge) := by
    funext k
    fin_cases k <;> apply Subtype.ext <;> decide
  change (∑ p : Fin 3, edgeTerm ℤ compositionInner p) = _
  rw [Fin.sum_univ_three]
  simp [edgeTerm, h0, h1, h2, hs, ho]
-- 色を逆にした 101 では、同じ辺⊗辺の切断の符号が負になる。
example : edgeSign (![1, 0, 1] : Fin 3 → Fin 2) 1 = -1 := by decide
-- 頂点への正次数作用は退化し、辺の非零項の総次数は語次数+1。
example : vertexValue ℤ compositionInner 0 = 0 := rfl
example : ∑ k : Fin 2, simplexDegree (edgeOutput compositionInner 1 k) = 2 :=
  edgeOutput_total_degree compositionInner 1 (by decide)
-- arity 二の標準 AW の二つの切断は辺⊗一と零⊗辺。
example : edgeOutput (permutationWord (1 : Equiv.Perm (Fin 2))) 0 0 = IntervalCuts.edge := by
  apply Subtype.ext
  decide
example : edgeOutput (permutationWord (1 : Equiv.Perm (Fin 2))) 0 1 = IntervalCuts.vertex 1 := by
  apply Subtype.ext
  decide
example : edgeOutput (permutationWord (1 : Equiv.Perm (Fin 2))) 1 0 = IntervalCuts.vertex 0 := by
  apply Subtype.ext
  decide
example : edgeOutput (permutationWord (1 : Equiv.Perm (Fin 2))) 1 1 = IntervalCuts.edge := by
  apply Subtype.ext
  decide

-- 同じ 010 の切断が、実際の N_*(Δ¹) の反復テンソルの次数 −2 に入る。
example : edgeComponent ℤ 2 1 (basis ℤ 2 1 (ULift.up compositionInner)) =
    tensorVectorOfDegree ℤ 2 2 (fun _ : Fin 2 => IntervalCuts.edge) (by decide) := by
  rw [edgeComponent_basis]
  have h0 : ¬ EdgeNondegenerate compositionInner.val 0 := by decide
  have h1 : EdgeNondegenerate compositionInner.val 1 := by decide
  have h2 : ¬ EdgeNondegenerate compositionInner.val 2 := by decide
  have hs : edgeSign compositionInner.val 1 = 1 := by decide
  have ho : edgeOutput compositionInner 1 = (fun _ : Fin 2 => IntervalCuts.edge) := by
    funext k
    fin_cases k <;> apply Subtype.ext <;> decide
  simp [edgeComponentOnWord, Fin.sum_univ_three, h0, h1, h2, hs, ho]
-- 実際の正規化区間の高次は退化によって零になる。
example : CategoryTheory.Limits.IsZero ((intervalChains ℤ).X 2) :=
  intervalChains_isZero ℤ 2 (by decide)
example : CategoryTheory.Limits.IsZero ((IntervalCuts.interval ℤ).X 1) :=
  interval_isZero_positive ℤ 1 (by decide)
-- 頂点への正次数の実際の成分も零。
example : vertexComponent ℤ 2 1 1 (basis ℤ 2 1 (ULift.up compositionInner)) = 0 := by
  rw [vertexComponent_basis]
  exact vertexComponentOnWord_eq_zero_of_positive ℤ compositionInner (by decide) 1

-- 二つの辺の後の因子を微分する境界項には負符号が付く。
open HomologicalComplex in
example : tensorBoundaryTerm ℤ 2 (fun _ => IntervalCuts.edge) 1 =
    -ιTensorObj (IntervalCuts.interval ℤ)
      (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 1) (-1) 0 (-1) (by decide)
      (faceVector ℤ IntervalCuts.edge ⊗ₜ[ℤ]
        tensorBoundaryTerm ℤ 1 (fun _ => IntervalCuts.edge) 0) := by
  change (-1 : ℤ).negOnePow •
    ιTensorObj (IntervalCuts.interval ℤ)
      (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 1) (-1) 0 (-1) _
      (faceVector ℤ IntervalCuts.edge ⊗ₜ[ℤ]
        tensorBoundaryTerm ℤ 1 (fun _ => IntervalCuts.edge) 0) = _
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.smul_def,
    Units.val_neg, Units.val_one, neg_one_zsmul]
-- 同じ頂点である必要はなく、任意の三つの端点のテンソルは実際に閉じている。
example (b : Fin 3 → Fin 2) :
    (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d 0 1
      (tensorVectorOfDegree ℤ 3 0 (fun i => IntervalCuts.vertex (b i))
        (by rw [tupleDegree_eq_sum]; simp)) = 0 :=
  tensorVectorOfDegree_d_eq_zero ℤ 3 0 _ _ (tensorVector_d_eq_zero_of_vertices ℤ 3 b)

-- 010 の左右の反復文字の削除は、それぞれ実際の語 10 と 01 を返す。
private def cutEraseLeft : BasisWord 2 0 :=
  eraseCutBasisWord compositionInner 1 0 (by decide) (by decide) ⟨2, by decide⟩
private def cutEraseRight : BasisWord 2 0 :=
  eraseCutBasisWord compositionInner 1 2 (by decide) (by decide) ⟨0, by decide⟩
example : cutEraseLeft.val = ![1, 0] := by funext i; fin_cases i <;> rfl
example : cutEraseRight.val = ![0, 1] := by funext i; fin_cases i <;> rfl
-- 残した切断点での全出力族は、元の辺を終点・始点へ置換したもの。
example : edgeOutput cutEraseLeft 0 =
    Function.update (edgeOutput compositionInner 1) 0 (IntervalCuts.vertex 1) :=
  edgeOutput_eraseCut_left compositionInner 0 0 (by decide) (by decide) ⟨2, by decide⟩
example : edgeOutput cutEraseRight 1 =
    Function.update (edgeOutput compositionInner 1) 0 (IntervalCuts.vertex 0) :=
  edgeOutput_eraseCut_right compositionInner 2 1 (by decide) (by decide) ⟨0, by decide⟩
-- 0102 の切断では第三の色は頂点なので、実際の境界和は二つの活動位置だけ。
example :
    (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d
        (-(tupleDegree 3 (edgeOutput compositionOuter 1) : ℤ))
        (-(tupleDegree 3 (edgeOutput compositionOuter 1) : ℤ) + 1)
        (tensorVector ℤ 3 (edgeOutput compositionOuter 1)) =
      tensorBoundaryTerm ℤ 3 (edgeOutput compositionOuter 1) 0 +
        tensorBoundaryTerm ℤ 3 (edgeOutput compositionOuter 1) 1 := by
  have hs : activePositions compositionOuter.val 1 = {0, 1} := by decide
  simpa only [hs, Finset.sum_pair (by decide : (0 : Fin 4) ≠ (1 : Fin 4))]
    using! edgeOutput_tensorVector_d ℤ compositionOuter 1 (by decide)

-- 三つの活動色 2,0,1 を持つ語。最初の色0の削除係数と残りの交換符号はともに負。
private def cutSignWord : BasisWord 3 2 := ⟨![2, 0, 1, 2, 0], by decide⟩
example : deletionCoefficient cutSignWord.val 1 = -1 ∧
    edgeSign (erase cutSignWord.val 1) 1 = -1 := by decide
-- 左出現の削除は、元の実際の切断と削除語の実際の切断の係数を保つ。
example : edgeSign cutSignWord.val 2 =
    deletionCoefficient cutSignWord.val 1 * edgeSign (erase cutSignWord.val 1) 1 := by
  have h := edgeSign_erase_left_boundary cutSignWord 1 1 (by decide) (by decide)
  rw [show (1 : Fin 5).succAbove (1 : Fin 4) = 2 by decide] at h
  have hp : (∑ k ∈ Finset.univ.filter (fun k : Fin 3 => k < cutSignWord.val 1),
      simplexDegree (edgeOutput cutSignWord 2 k)) = 0 := by decide
  simpa only [hp, pow_zero, mul_one] using h
-- 同じ色の右出現を削除する場合は、始点側の負の境界係数になる。
example : -edgeSign cutSignWord.val 2 =
    deletionCoefficient cutSignWord.val 4 * edgeSign (erase cutSignWord.val 4) 2 := by
  have h := edgeSign_erase_right_boundary cutSignWord 4 1 2
    (by decide) (by decide) (by decide)
  rw [show (4 : Fin 5).succAbove (2 : Fin 4) = 2 by decide] at h
  have hp : (∑ k ∈ Finset.univ.filter (fun k : Fin 3 => k < cutSignWord.val 1),
      simplexDegree (edgeOutput cutSignWord 2 k)) = 0 := by decide
  simpa only [hp, pow_zero, mul_one] using h

-- 010 の辺を端点に置換した実際のテンソルが、削除語の切断テンソルになる。
example : endpointTensor ℤ 2 (edgeOutput compositionInner 1) 0 (by decide) 1 =
    tensorVectorAt ℤ 2 (edgeOutput cutEraseLeft 0) (-1) (by decide) := by
  simpa only [show (0 : Fin 3).succAbove (0 : Fin 2) = 1 by decide]
    using! endpointTensor_eraseCut_left ℤ compositionInner 0 0
      (by decide) (by decide) ⟨2, by decide⟩
example : endpointTensor ℤ 2 (edgeOutput compositionInner 1) 0 (by decide) 0 =
    tensorVectorAt ℤ 2 (edgeOutput cutEraseRight 1) (-1) (by decide) := by
  simpa only [show (2 : Fin 3).succAbove (1 : Fin 2) = 1 by decide]
    using! endpointTensor_eraseCut_right ℤ compositionInner 2 1
      (by decide) (by decide) ⟨0, by decide⟩
-- 三つの辺の真ん中の色を微分すると、奇数の前方次数で終点側が負になる。
private def factorSignWord : BasisWord 3 2 := ⟨![1, 2, 0, 1, 2], by decide⟩
example : tensorBoundaryTerm ℤ 3 (edgeOutput factorSignWord 2) 1 =
    -endpointTensor ℤ 3 (edgeOutput factorSignWord 2) 1 (by decide) 1 +
      endpointTensor ℤ 3 (edgeOutput factorSignWord 2) 1 (by decide) 0 := by
  have h := cut_factor_boundary ℤ factorSignWord 0 3 1 2
    (by decide) (by decide) (by decide) (by decide)
  have hp : (0 : Fin 5).succAbove (1 : Fin 4) = 2 := by decide
  have hs : edgeSign factorSignWord.val 2 = 1 := by decide
  have hL : deletionCoefficient factorSignWord.val 0 *
      edgeSign (erase factorSignWord.val 0) 1 = -1 := by decide
  have hR : deletionCoefficient factorSignWord.val 3 *
      edgeSign (erase factorSignWord.val 3) 2 = 1 := by decide
  simpa only [hp, hs, hL, hR, one_smul, neg_one_zsmul] using! h

-- 01020 の最初の0を削除すると非零だが、元の切断は左側の重複で退化する。
private def residualWord : BasisWord 3 2 := ⟨![0, 1, 0, 2, 0], by decide⟩
private def residualFixture : NonpivotResidualCut residualWord.val where
  deleted := 0
  pivot := 2
  defect := 2
  nondegenerate := by decide
  defect_spec := by decide
  defect_ne_pivot := by decide
example : ¬ EdgeNondegenerate residualWord.val 3 := by decide
-- 交換相手は中央の0の削除で、同じ元切断点に戻る。二回交換すると厳密に元へ戻る。
example : residualFixture.swap.pivot = 2 := by
  apply (Fin.succAbove_right_injective (p := (2 : Fin 5)))
  exact residualFixture.partnerPosition_spec.1
example : residualFixture.swap.swap = residualFixture := residualFixture.swap_swap
example : residualFixture.swap ≠ residualFixture := residualFixture.swap_ne
example : (residualCutBasisWord residualWord residualFixture).val = ![1, 0, 2, 0] := by
  funext i
  fin_cases i <;> rfl
example : (residualCutBasisWord residualWord residualFixture.swap).val = ![0, 1, 2, 0] := by
  funext i
  fin_cases i <;> rfl
-- この相殺対の削除係数と切断符号の積は互いに反対。
example : deletionCoefficient residualWord.val 0 * edgeSign (erase residualWord.val 0) 2 =
    -(deletionCoefficient residualWord.val 2 * edgeSign (erase residualWord.val 2) 2) := by decide
-- 語は異なっても、実際の正規化区間テンソルでの切断値は同じ。
example :
    tensorVectorOfDegree ℤ 3 2 (edgeOutput (residualCutBasisWord residualWord residualFixture) 2)
        (edgeOutput_tupleDegree _ _ residualFixture.nondegenerate) =
      tensorVectorOfDegree ℤ 3 2
        (edgeOutput (residualCutBasisWord residualWord residualFixture.swap)
          residualFixture.swap.pivot)
        (edgeOutput_tupleDegree _ _ residualFixture.swap.nondegenerate) :=
  residualCut_tensor_eq ℤ residualWord residualFixture

-- 010210 は二つの区切りの削除係数が同じでも、切断符号が反転する三出現例。
private def residualTripleWord : BasisWord 3 3 := ⟨![0, 1, 0, 2, 1, 0], by decide⟩
private def residualTripleFixture : NonpivotResidualCut residualTripleWord.val where
  deleted := 0
  pivot := 2
  defect := 2
  nondegenerate := by decide
  defect_spec := by decide
  defect_ne_pivot := by decide
example : deletionCoefficient residualTripleWord.val 0 = 1 ∧
    deletionCoefficient residualTripleWord.val 2 = 1 ∧
    edgeSign (erase residualTripleWord.val 0) 2 = -1 ∧
    edgeSign (erase residualTripleWord.val 2) 2 = 1 := by decide
example : deletionCoefficient residualTripleWord.val residualTripleFixture.deleted *
      edgeSign (erase residualTripleWord.val residualTripleFixture.deleted)
        residualTripleFixture.pivot =
    -(deletionCoefficient residualTripleWord.val residualTripleFixture.swap.deleted *
      edgeSign (erase residualTripleWord.val residualTripleFixture.swap.deleted)
        residualTripleFixture.swap.pivot) := residualTripleFixture.swap_coefficient

-- 左側の最終出現との交換。切断符号は等しく、削除係数が反対になる。
private def residualFinalWord : BasisWord 3 2 := ⟨![0, 1, 0, 2, 1], by decide⟩
private def residualFinalFixture : NonpivotResidualCut residualFinalWord.val where
  deleted := 0
  pivot := 2
  defect := 2
  nondegenerate := by decide
  defect_spec := by decide
  defect_ne_pivot := by decide
example : ¬ Caesura residualFinalWord.val 2 := by decide
example : deletionCoefficient residualFinalWord.val residualFinalFixture.deleted *
      edgeSign (erase residualFinalWord.val residualFinalFixture.deleted)
        residualFinalFixture.pivot =
    -(deletionCoefficient residualFinalWord.val residualFinalFixture.swap.deleted *
      edgeSign (erase residualFinalWord.val residualFinalFixture.swap.deleted)
        residualFinalFixture.swap.pivot) := residualFinalFixture.swap_coefficient

-- 同じ最終出現交換の右側版と、その逆順も一般定理から得る。
private def residualRightFixture : NonpivotResidualCut residualWord.val where
  deleted := 2
  pivot := 1
  defect := 4
  nondegenerate := by decide
  defect_spec := by decide
  defect_ne_pivot := by decide
example : deletionCoefficient residualWord.val residualRightFixture.deleted *
      edgeSign (erase residualWord.val residualRightFixture.deleted) residualRightFixture.pivot =
    -(deletionCoefficient residualWord.val residualRightFixture.swap.deleted *
      edgeSign (erase residualWord.val residualRightFixture.swap.deleted)
        residualRightFixture.swap.pivot) := residualRightFixture.swap_coefficient
example : deletionCoefficient residualWord.val residualRightFixture.swap.deleted *
      edgeSign (erase residualWord.val residualRightFixture.swap.deleted)
        residualRightFixture.swap.pivot =
    -(deletionCoefficient residualWord.val residualRightFixture.deleted *
      edgeSign (erase residualWord.val residualRightFixture.deleted) residualRightFixture.pivot) := by
  simpa only [NonpivotResidualCut.swap_swap] using residualRightFixture.swap.swap_coefficient

-- 全添字の和も実際の ℤ 上の区間テンソルで零となる。
example : ∑ c : NonpivotResidualCut residualTripleWord.val,
    (deletionCoefficient residualTripleWord.val c.deleted *
      edgeSign (erase residualTripleWord.val c.deleted) c.pivot) •
      tensorVectorOfDegree ℤ 3 3 (edgeOutput (residualCutBasisWord residualTripleWord c) c.pivot)
        (edgeOutput_tupleDegree _ _ c.nondegenerate) = 0 :=
  residualCut_tensor_sum_eq_zero ℤ residualTripleWord

-- 01203 の非零切断は隣接する1,2の二つ。内部の端点置換は同じ隙間値。
private def pivotIntervalWord : BasisWord 4 1 := ⟨![0, 1, 2, 0, 3], by decide⟩
example : Function.update (edgeOutput pivotIntervalWord 1) 1 (IntervalCuts.vertex 0) =
    Function.update (edgeOutput pivotIntervalWord 2) 2 (IntervalCuts.vertex 1) := by
  rw [show (1 : Fin 4) = pivotIntervalWord.val 1 by rfl,
    show (2 : Fin 4) = pivotIntervalWord.val 2 by rfl,
    edgeOutput_pivot_endpoint_zero pivotIntervalWord 1 (by decide),
    edgeOutput_pivot_endpoint_one pivotIntervalWord 2 (by decide)]
  rfl
-- 共通係数は負で、実際の全因子境界和では内部項が消え、二端点だけが残る。
example : ∑ p, pivotBoundaryValue ℤ pivotIntervalWord p =
    -(gapTensor ℤ pivotIntervalWord 1 - gapTensor ℤ pivotIntervalWord 3) := by
  have h := pivotBoundaryValue_sum_of_endpoints ℤ pivotIntervalWord 1 2
    (by decide) (by decide) (by decide)
  have hs : (-1 : ℤ) ^ (Finset.univ.filter (Caesura pivotIntervalWord.val)).card *
      (-1 : ℤ) ^ positionInversionCount pivotIntervalWord.val
        (Finset.univ.filter (Caesura pivotIntervalWord.val)) = -1 := by decide
  simpa only [hs, neg_one_zsmul] using! h
-- 同色三出現の語には非零切断がなく、全和も実際に零。
example : ∑ p, pivotBoundaryValue ℤ residualWord p = 0 := by
  have hs : ¬ (Finset.univ.filter (EdgeNondegenerate residualWord.val)).Nonempty := by decide
  simpa only [dite_eq_right hs] using! pivotBoundaryValue_sum ℤ residualWord
-- 次数零では全 arity・全置換語について入力辺の境界へ一致する。
example {n : ℕ} (u : BasisWord n 0) : ∑ p, pivotBoundaryValue ℤ u p =
    tensorVectorOfDegree ℤ n 0 (fun _ => IntervalCuts.vertex 1) (vertex_tupleDegree n 1) -
      tensorVectorOfDegree ℤ n 0 (fun _ => IntervalCuts.vertex 0) (vertex_tupleDegree n 0) :=
  pivotBoundaryValue_sum_zeroDegree ℤ u

-- 01202 の元の辺切断は全て退化するが、隙間3は非退化。
private def gapOnlyWord : BasisWord 3 2 := ⟨![0, 1, 2, 0, 2], by decide⟩
example : ∀ p, ¬ EdgeNondegenerate gapOnlyWord.val p := by decide
example : GapNondegenerate gapOnlyWord.val 3 := by decide
-- 隙間の右隣3には左の0、左隣2には右の2が一意な削除相手となる。
example : ∃! i, i < (3 : Fin 5) ∧ gapOnlyWord.val i = gapOnlyWord.val 3 :=
  gap_before_defect_existsUnique gapOnlyWord.val 3 (by decide) (by decide)
example : ∃! i, (2 : Fin 5) < i ∧ gapOnlyWord.val i = gapOnlyWord.val 2 :=
  gap_after_defect_existsUnique gapOnlyWord.val 2 (by decide) (by decide)
example : EdgeNondegenerate (erase gapOnlyWord.val 0) 2 :=
  erase_edgeNondegenerate_of_gap_before gapOnlyWord.val 0 2
    (by decide) (by decide) (by decide)
example : EdgeNondegenerate (erase gapOnlyWord.val 4) 2 :=
  erase_edgeNondegenerate_of_gap_after gapOnlyWord.val 4 2
    (by decide) (by decide) (by decide)
-- 二つの異なる実際の削除語は、それぞれ同じ隙間3のテンソル値へ戻る。
private def gapOnlyLeft : BasisWord 3 1 :=
  pivotEraseBasisWord gapOnlyWord 0 2 (by decide) (by decide)
private def gapOnlyRight : BasisWord 3 1 :=
  pivotEraseBasisWord gapOnlyWord 4 2 (by decide) (by decide)
example : gapOnlyLeft.val = ![1, 2, 0, 2] := by funext i; fin_cases i <;> rfl
example : gapOnlyRight.val = ![0, 1, 2, 0] := by funext i; fin_cases i <;> rfl
example : tensorVectorOfDegree ℤ 3 2 (edgeOutput gapOnlyLeft 2)
      (edgeOutput_tupleDegree _ _ (by decide)) = gapTensor ℤ gapOnlyWord 3 :=
  pivotErase_tensor_before ℤ gapOnlyWord 0 2 (by decide) (by decide) (by decide)
example : tensorVectorOfDegree ℤ 3 2 (edgeOutput gapOnlyRight 2)
      (edgeOutput_tupleDegree _ _ (by decide)) = gapTensor ℤ gapOnlyWord 3 :=
  pivotErase_tensor_after ℤ gapOnlyWord 4 2 (by decide) (by decide) (by decide)
-- この空の元切断区間の例の具体的な二係数。一般公式による同じ相殺は下で検証。
example : deletionCoefficient gapOnlyWord.val 0 * edgeSign (erase gapOnlyWord.val 0) 2 = -1 ∧
    deletionCoefficient gapOnlyWord.val 4 * edgeSign (erase gapOnlyWord.val 4) 2 = 1 := by decide

-- 01202 の二削除の相殺を一般の係数・実際のテンソル公式で検証する。
example : (deletionCoefficient gapOnlyWord.val 0 * edgeSign (erase gapOnlyWord.val 0) 2) •
      tensorVectorOfDegree ℤ 3 2 (edgeOutput gapOnlyLeft 2)
        (edgeOutput_tupleDegree _ _ (by decide)) +
    (deletionCoefficient gapOnlyWord.val 4 * edgeSign (erase gapOnlyWord.val 4) 2) •
      tensorVectorOfDegree ℤ 3 2 (edgeOutput gapOnlyRight 2)
        (edgeOutput_tupleDegree _ _ (by decide)) = 0 :=
  pivotDeletion_weighted_pair ℤ gapOnlyWord 0 4 2 2 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
-- 色を置換した20121では区切り色の逆転数が奇数なので、両係数の符号が反転する。
private def gapOddWord : BasisWord 3 2 := ⟨![2, 0, 1, 2, 1], by decide⟩
example : (-1 : ℤ) ^ (Finset.univ.filter (Caesura gapOddWord.val)).card *
    (-1 : ℤ) ^ positionInversionCount gapOddWord.val
      (Finset.univ.filter (Caesura gapOddWord.val)) = -1 := by decide
example : deletionCoefficient gapOddWord.val 0 * edgeSign (erase gapOddWord.val 0) 2 = 1 := by
  have h := pivotDeletion_coefficient_before gapOddWord.val 0 2
    (by decide) (by decide) (by decide)
  have hc : (-1 : ℤ) ^ (Finset.univ.filter (Caesura gapOddWord.val)).card *
      (-1 : ℤ) ^ positionInversionCount gapOddWord.val
        (Finset.univ.filter (Caesura gapOddWord.val)) = -1 := by decide
  simpa only [hc, neg_neg] using h
example : deletionCoefficient gapOddWord.val 4 * edgeSign (erase gapOddWord.val 4) 2 = -1 := by
  have h := pivotDeletion_coefficient_after gapOddWord.val 4 2
    (by decide) (by decide) (by decide)
  have hc : (-1 : ℤ) ^ (Finset.univ.filter (Caesura gapOddWord.val)).card *
      (-1 : ℤ) ^ positionInversionCount gapOddWord.val
        (Finset.univ.filter (Caesura gapOddWord.val)) = -1 := by decide
  simpa only [hc] using h

-- 01202 の全左右削除添字は、それぞれ一つの隙間隣接退化切断へ対応する。
example : Fintype.card (PivotResidualCut.Before gapOnlyWord.val) = 1 := by
  rw [Fintype.card_congr (PivotResidualCut.beforeEquiv (u := gapOnlyWord.val))]
  decide
example : Fintype.card (PivotResidualCut.After gapOnlyWord.val) = 1 := by
  rw [Fintype.card_congr (PivotResidualCut.afterEquiv (u := gapOnlyWord.val))]
  decide
-- 二つの既知項だけでなく、実際の全切断点障害削除和も零になる。
example : ∑ c, pivotResidualValue ℤ gapOnlyWord c = 0 := by
  rw [pivotResidualValue_sum_eq_boundary]
  apply Finset.sum_eq_zero
  intro p _
  have hn : ¬ EdgeNondegenerate gapOnlyWord.val p := by fin_cases p <;> decide
  simp only [pivotBoundaryValue, dite_eq_right hn]
-- 非零元切断が二つある01203でも、全削除和は同じ実際の両端隙間差へ一致する。
example : ∑ c, pivotResidualValue ℤ pivotIntervalWord c =
    -(gapTensor ℤ pivotIntervalWord 1 - gapTensor ℤ pivotIntervalWord 3) := by
  rw [pivotResidualValue_sum_eq_boundary]
  have h := pivotBoundaryValue_sum_of_endpoints ℤ pivotIntervalWord 1 2
    (by decide) (by decide) (by decide)
  have hs : (-1 : ℤ) ^ (Finset.univ.filter (Caesura pivotIntervalWord.val)).card *
      (-1 : ℤ) ^ positionInversionCount pivotIntervalWord.val
        (Finset.univ.filter (Caesura pivotIntervalWord.val)) = -1 := by decide
  simpa only [hs, neg_one_zsmul] using! h

-- 01202 では非切断点・切断点障害を全て含む正規化全削除和が相殺する。
example : ∑ c, normalizedDeletedValue ℤ gapOnlyWord c = 0 :=
  normalizedDeletedValue_sum_eq_zero_of_no_cut ℤ gapOnlyWord (by decide)
-- 三出現の01020でも正規化全削除和が零となる。
example : ∑ c, normalizedDeletedValue ℤ residualWord c = 0 :=
  normalizedDeletedValue_sum_eq_zero_of_no_cut ℤ residualWord (by decide)
-- 元切断が非零の010では、実際の全削除和は元切断非零部分と切断点境界部分へ分かれる。
example : ∑ c, normalizedDeletedValue ℤ compositionInner c =
    (∑ c : NormalizedDeletedCut.Regular compositionInner.val,
      normalizedDeletedValue ℤ compositionInner c.val) +
        ∑ p, pivotBoundaryValue ℤ compositionInner p :=
  normalizedDeletedValue_sum_reduce ℤ compositionInner

-- 非全射な00と、全射だが退化する001は、生成元上の実際の辺成分でも零。
example : edgeComponent ℤ 2 0 (generator ℤ (n := 2) (d := 0) (![0, 0] : Fin 2 → Fin 2)) = 0 := by
  have hn : ¬ Function.Surjective (![0, 0] : Fin 2 → Fin 2) := by decide
  simpa only [dite_eq_right hn] using!
    edgeComponent_generator ℤ (n := 2) (d := 0) (![0, 0] : Fin 2 → Fin 2)
example : edgeComponent ℤ 2 1 (generator ℤ (n := 2) (d := 1) (![0, 0, 1] : Fin 3 → Fin 2)) = 0 := by
  rw [edgeComponent_generator, dite_eq_left (by decide)]
  apply Finset.sum_eq_zero
  intro p _
  have hn : ∀ q : Fin 3, ¬ EdgeNondegenerate (![0, 0, 1] : Fin 3 → Fin 2) q := by decide
  exact False.elim (hn p.val p.property)
-- 正規化和だけでなく、01202と01020の実際の削除微分の辺成分も全体として零。
example : edgeComponent ℤ 3 1 (differentialOnWord ℤ gapOnlyWord) = 0 :=
  edgeComponent_differentialOnWord_eq_zero_of_no_cut ℤ gapOnlyWord (by decide)
example : edgeComponent ℤ 3 1 (differentialOnWord ℤ residualWord) = 0 :=
  edgeComponent_differentialOnWord_eq_zero_of_no_cut ℤ residualWord (by decide)
-- 010の非零元切断部分も、同じ実際の微分成分から直接取り出せる。
example : edgeComponent ℤ 2 0 (differentialOnWord ℤ compositionInner) =
    (∑ c : NormalizedDeletedCut.Regular compositionInner.val,
      normalizedDeletedValue ℤ compositionInner c.val) +
        ∑ p, pivotBoundaryValue ℤ compositionInner p :=
  edgeComponent_differentialOnWord_reduce ℤ compositionInner

-- 010の反復色位置対は一つで、左右二削除が元切断非零部分の全添字となる。
example : Fintype.card (NormalizedDeletedCut.Regular compositionInner.val) = 2 := by
  have hc : Fintype.card (RepeatCutPair compositionInner.val) = 1 := by
    rw [Fintype.card_congr (repeatPairFiberEquiv (u := compositionInner.val))]
    decide
  rw [← Fintype.card_congr (regularCutEquiv compositionInner), Fintype.card_prod, hc]
  decide
-- 010と、交換符号が非自明な20120の実際の辺成分が削除微分と可換する。
example : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 2).d (-2) (-1)
    (edgeComponentOnWord ℤ compositionInner) =
      edgeComponent ℤ 2 0 (differentialOnWord ℤ compositionInner) := by
  simpa only using! edgeComponentOnWord_d_positive ℤ compositionInner
example : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d (-3) (-2)
    (edgeComponentOnWord ℤ cutSignWord) =
      edgeComponent ℤ 3 1 (differentialOnWord ℤ cutSignWord) := by
  simpa only using! edgeComponentOnWord_d_positive ℤ cutSignWord
-- 次数零の置換語とarity零の空語も、入力辺の二頂点差へ一致する。
private def zeroPermutationWord : BasisWord 3 0 := ⟨![2, 0, 1], by decide⟩
private def zeroEmptyWord : BasisWord 0 0 := ⟨Fin.elim0, by decide⟩
example : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d (-1) 0
    (edgeComponentOnWord ℤ zeroPermutationWord) =
      vertexComponentOnWord ℤ zeroPermutationWord 1 -
        vertexComponentOnWord ℤ zeroPermutationWord 0 :=
  edgeComponentOnWord_d_zero ℤ zeroPermutationWord
example : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 0).d (-1) 0
    (edgeComponentOnWord ℤ zeroEmptyWord) =
      vertexComponentOnWord ℤ zeroEmptyWord 1 - vertexComponentOnWord ℤ zeroEmptyWord 0 :=
  edgeComponentOnWord_d_zero ℤ zeroEmptyWord

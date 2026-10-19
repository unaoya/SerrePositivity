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
      `SerrePositivity.EInfinity.TableReduction.reverse_block_extraction] do
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

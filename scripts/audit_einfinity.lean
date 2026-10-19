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
      `SerrePositivity.EInfinity.Surjection.componentHorizontalExtraction_success] do
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

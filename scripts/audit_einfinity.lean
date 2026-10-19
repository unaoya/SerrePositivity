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
      `SerrePositivity.EInfinity.TableReduction.degreeMap_basis] do
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

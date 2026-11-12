import SerrePositivity.KST.ProExcision
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedEZHomotopy
/-!
概要：K-L6 が所有する公開宣言の型と公理を監査する。
方針：各宣言の型と公理集合を表示する。
規約：標準三公理 propext・Classical.choice・Quot.sound のみを許す。
使われ方：KST §4・App. A の各保存単位。
-/
set_option pp.universes true
set_option pp.explicit true

#check @SerrePositivity.KST.ProExcision.Tower
#print axioms SerrePositivity.KST.ProExcision.Tower

#check @SerrePositivity.KST.ProExcision.Tower.constant
#print axioms SerrePositivity.KST.ProExcision.Tower.constant

#check @SerrePositivity.KST.ProExcision.Tower.map
#print axioms SerrePositivity.KST.ProExcision.Tower.map

#check @SerrePositivity.KST.ProExcision.LevelHom
#print axioms SerrePositivity.KST.ProExcision.LevelHom

#check @SerrePositivity.KST.ProExcision.LevelHom.id
#print axioms SerrePositivity.KST.ProExcision.LevelHom.id

#check @SerrePositivity.KST.ProExcision.LevelHom.comp
#print axioms SerrePositivity.KST.ProExcision.LevelHom.comp

#check @SerrePositivity.KST.ProExcision.LevelHom.map
#print axioms SerrePositivity.KST.ProExcision.LevelHom.map

#check @SerrePositivity.KST.ProExcision.IsProIso
#print axioms SerrePositivity.KST.ProExcision.IsProIso

#check @SerrePositivity.KST.ProExcision.IsProIso.id
#print axioms SerrePositivity.KST.ProExcision.IsProIso.id

#check @SerrePositivity.KST.ProExcision.IsProIso.map
#print axioms SerrePositivity.KST.ProExcision.IsProIso.map

#check @SerrePositivity.KST.ProExcision.IsProIso.comp
#print axioms SerrePositivity.KST.ProExcision.IsProIso.comp

#check @SerrePositivity.KST.ProExcision.IsProIso.constant_inverse
#print axioms SerrePositivity.KST.ProExcision.IsProIso.constant_inverse

#check @SerrePositivity.KST.ProExcision.diagonal_cofinal
#print axioms SerrePositivity.KST.ProExcision.diagonal_cofinal

#check @SerrePositivity.KST.ProExcision.Tower.reindex
#print axioms SerrePositivity.KST.ProExcision.Tower.reindex

#check @SerrePositivity.KST.ProExcision.Tower.reindexHom
#print axioms SerrePositivity.KST.ProExcision.Tower.reindexHom

#check @SerrePositivity.KST.ProExcision.Tower.reindexHom_isProIso
#print axioms SerrePositivity.KST.ProExcision.Tower.reindexHom_isProIso

#check @SerrePositivity.KST.ProExcision.IsProZero
#print axioms SerrePositivity.KST.ProExcision.IsProZero

#check @SerrePositivity.KST.ProExcision.IsProZero.map
#print axioms SerrePositivity.KST.ProExcision.IsProZero.map

#check @SerrePositivity.KST.ProExcision.IsProZero.reindex
#print axioms SerrePositivity.KST.ProExcision.IsProZero.reindex

#check @SerrePositivity.KST.ProExcision.IsProEquivalence
#print axioms SerrePositivity.KST.ProExcision.IsProEquivalence

#check @SerrePositivity.KST.ProExcision.IsProCartesian
#print axioms SerrePositivity.KST.ProExcision.IsProCartesian

#check @SerrePositivity.KST.ProExcision.Tower.transition_apply
#print axioms SerrePositivity.KST.ProExcision.Tower.transition_apply

#check @SerrePositivity.KST.ProExcision.LevelHom.naturality_apply
#print axioms SerrePositivity.KST.ProExcision.LevelHom.naturality_apply

#check @SerrePositivity.KST.ProExcision.IsProMono
#print axioms SerrePositivity.KST.ProExcision.IsProMono

#check @SerrePositivity.KST.ProExcision.IsProEpi
#print axioms SerrePositivity.KST.ProExcision.IsProEpi

#check @SerrePositivity.KST.ProExcision.IsProIso.isProMono
#print axioms SerrePositivity.KST.ProExcision.IsProIso.isProMono

#check @SerrePositivity.KST.ProExcision.IsProIso.isProEpi
#print axioms SerrePositivity.KST.ProExcision.IsProIso.isProEpi

#check @SerrePositivity.KST.ProExcision.descendRange
#print axioms SerrePositivity.KST.ProExcision.descendRange

#check @SerrePositivity.KST.ProExcision.descendRange_apply
#print axioms SerrePositivity.KST.ProExcision.descendRange_apply

#check @SerrePositivity.KST.ProExcision.isProIso_of_mono_epi
#print axioms SerrePositivity.KST.ProExcision.isProIso_of_mono_epi

#check @SerrePositivity.KST.ProExcision.FiveTerm
#print axioms SerrePositivity.KST.ProExcision.FiveTerm

#check @SerrePositivity.KST.ProExcision.FiveTermHom
#print axioms SerrePositivity.KST.ProExcision.FiveTermHom

#check @SerrePositivity.KST.ProExcision.FiveTermHom.isProMono
#print axioms SerrePositivity.KST.ProExcision.FiveTermHom.isProMono

#check @SerrePositivity.KST.ProExcision.FiveTermHom.isProEpi
#print axioms SerrePositivity.KST.ProExcision.FiveTermHom.isProEpi

#check @SerrePositivity.KST.ProExcision.FiveTermHom.isProIso
#print axioms SerrePositivity.KST.ProExcision.FiveTermHom.isProIso

#check @SerrePositivity.KST.ProExcision.LevelwiseExactSequence
#print axioms SerrePositivity.KST.ProExcision.LevelwiseExactSequence

#check @SerrePositivity.KST.ProExcision.ExactTowerSequence
#print axioms SerrePositivity.KST.ProExcision.ExactTowerSequence

#check @SerrePositivity.KST.ProExcision.LevelwiseExactSequence.toTower
#print axioms SerrePositivity.KST.ProExcision.LevelwiseExactSequence.toTower

#check @SerrePositivity.KST.ProExcision.ExactTowerSequence.fiveTerm
#print axioms SerrePositivity.KST.ProExcision.ExactTowerSequence.fiveTerm

#check @SerrePositivity.KST.ProExcision.Tower.ofInverseDiagram
#print axioms SerrePositivity.KST.ProExcision.Tower.ofInverseDiagram

#check @SerrePositivity.KST.ProExcision.koszulTower
#print axioms SerrePositivity.KST.ProExcision.koszulTower

#check @SerrePositivity.KST.ProExcision.koszulHomologyTower
#print axioms SerrePositivity.KST.ProExcision.koszulHomologyTower

#check @SerrePositivity.KST.ProExcision.koszulHomologyTower_isProZero
#print axioms SerrePositivity.KST.ProExcision.koszulHomologyTower_isProZero

#check @SerrePositivity.KST.ProExcision.range_lTensor_le_ideal_smul
#print axioms SerrePositivity.KST.ProExcision.range_lTensor_le_ideal_smul

#check @SerrePositivity.KST.ProExcision.koszulTensorTower
#print axioms SerrePositivity.KST.ProExcision.koszulTensorTower

#check @SerrePositivity.KST.ProExcision.koszulTensorHomologyTower
#print axioms SerrePositivity.KST.ProExcision.koszulTensorHomologyTower

#check @SerrePositivity.KST.ProExcision.koszulTensorHomologyTower_isProZero
#print axioms SerrePositivity.KST.ProExcision.koszulTensorHomologyTower_isProZero

#check @SerrePositivity.KST.ProExcision.IsProZero.of_levelwiseIso
#print axioms SerrePositivity.KST.ProExcision.IsProZero.of_levelwiseIso

#check @SerrePositivity.KST.ProExcision.flatTensorHomologyIso
#print axioms SerrePositivity.KST.ProExcision.flatTensorHomologyIso

#check @SerrePositivity.KST.ProExcision.ideal_smul_tensor_range
#print axioms SerrePositivity.KST.ProExcision.ideal_smul_tensor_range

#check @SerrePositivity.KST.ProExcision.tensor_proZero
#print axioms SerrePositivity.KST.ProExcision.tensor_proZero

#check @SerrePositivity.KST.ProExcision.tensor_proIso
#print axioms SerrePositivity.KST.ProExcision.tensor_proIso

#check @SerrePositivity.KST.ProExcision.flatTensor_homologyMap_zero
#print axioms SerrePositivity.KST.ProExcision.flatTensor_homologyMap_zero

#check @SerrePositivity.KST.ProExcision.flatTensor_homology_proZero
#print axioms SerrePositivity.KST.ProExcision.flatTensor_homology_proZero

#check @SerrePositivity.KST.ProExcision.koszul_flatTensor_homology_proZero
#print axioms SerrePositivity.KST.ProExcision.koszul_flatTensor_homology_proZero

#check @SerrePositivity.KST.ProExcision.Tower.mapNatTrans
#print axioms SerrePositivity.KST.ProExcision.Tower.mapNatTrans

#check @SerrePositivity.KST.ProExcision.homologyMap_zero_of_component_zero
#print axioms SerrePositivity.KST.ProExcision.homologyMap_zero_of_component_zero

#check @SerrePositivity.KST.ProExcision.homology_proZero_of_component
#print axioms SerrePositivity.KST.ProExcision.homology_proZero_of_component

#check @SerrePositivity.KST.ProExcision.proZero_of_exact
#print axioms SerrePositivity.KST.ProExcision.proZero_of_exact

#check @SerrePositivity.KST.ProExcision.proIso_of_injective_exact_proZero
#print axioms SerrePositivity.KST.ProExcision.proIso_of_injective_exact_proZero

#check @SerrePositivity.KST.ProExcision.proZero_finite_extension
#print axioms SerrePositivity.KST.ProExcision.proZero_finite_extension

#check @SerrePositivity.KST.ProExcision.truncationInclusion
#print axioms SerrePositivity.KST.ProExcision.truncationInclusion

#check @SerrePositivity.KST.ProExcision.truncationInclusion_comp_inclusion
#print axioms SerrePositivity.KST.ProExcision.truncationInclusion_comp_inclusion

#check @SerrePositivity.KST.ProExcision.truncationFiltration
#print axioms SerrePositivity.KST.ProExcision.truncationFiltration

#check @SerrePositivity.KST.ProExcision.koszulTensorFiltration
#print axioms SerrePositivity.KST.ProExcision.koszulTensorFiltration

#check @SerrePositivity.KST.ProExcision.koszulFiltrationIndex
#print axioms SerrePositivity.KST.ProExcision.koszulFiltrationIndex

#check @SerrePositivity.KST.ProExcision.finiteKoszulTensorFiltration
#print axioms SerrePositivity.KST.ProExcision.finiteKoszulTensorFiltration

#check @SerrePositivity.KST.ProExcision.koszulTruncation_initial_isZero
#print axioms SerrePositivity.KST.ProExcision.koszulTruncation_initial_isZero

#check @SerrePositivity.KST.ProExcision.koszulTruncation_terminal_isIso
#print axioms SerrePositivity.KST.ProExcision.koszulTruncation_terminal_isIso

#check @SerrePositivity.KST.ProExcision.koszulTensorFiltration_initial_isZero
#print axioms SerrePositivity.KST.ProExcision.koszulTensorFiltration_initial_isZero

#check @SerrePositivity.KST.ProExcision.truncationMap_comp_inclusion
#print axioms SerrePositivity.KST.ProExcision.truncationMap_comp_inclusion

#check @SerrePositivity.KST.ProExcision.truncationInclusion_naturality
#print axioms SerrePositivity.KST.ProExcision.truncationInclusion_naturality

#check @SerrePositivity.KST.ProExcision.truncationFiltrationMap
#print axioms SerrePositivity.KST.ProExcision.truncationFiltrationMap

#check @SerrePositivity.KST.ProExcision.truncationFiltrationFunctor
#print axioms SerrePositivity.KST.ProExcision.truncationFiltrationFunctor

#check @SerrePositivity.KST.ProExcision.truncationGradeIso
#print axioms SerrePositivity.KST.ProExcision.truncationGradeIso

#check @SerrePositivity.KST.ProExcision.tensorCutShortComplex
#print axioms SerrePositivity.KST.ProExcision.tensorCutShortComplex

#check @SerrePositivity.KST.ProExcision.tensorCutShortComplex_shortExact
#print axioms SerrePositivity.KST.ProExcision.tensorCutShortComplex_shortExact

#check @SerrePositivity.KST.ProExcision.tensorCutConeComparison
#print axioms SerrePositivity.KST.ProExcision.tensorCutConeComparison

#check @SerrePositivity.KST.ProExcision.tensorCutConeComparison_quasiIso
#print axioms SerrePositivity.KST.ProExcision.tensorCutConeComparison_quasiIso

#check @SerrePositivity.KST.ProExcision.tensorCutGradeIso
#print axioms SerrePositivity.KST.ProExcision.tensorCutGradeIso

#check @SerrePositivity.KST.ProExcision.tensorCutConeHomologyIso
#print axioms SerrePositivity.KST.ProExcision.tensorCutConeHomologyIso

#check @SerrePositivity.KST.ProExcision.aboveAboveIso_comp_inclusion
#print axioms SerrePositivity.KST.ProExcision.aboveAboveIso_comp_inclusion

#check @SerrePositivity.KST.ProExcision.aboveAboveIso_inv_comp_inclusion
#print axioms SerrePositivity.KST.ProExcision.aboveAboveIso_inv_comp_inclusion

#check @SerrePositivity.KST.ProExcision.adjacentTensorConeIso
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorConeIso

#check @SerrePositivity.KST.ProExcision.adjacentTensorConeHomologyIso
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorConeHomologyIso

#check @SerrePositivity.KST.ProExcision.singleTensorShiftIso
#print axioms SerrePositivity.KST.ProExcision.singleTensorShiftIso

#check @SerrePositivity.KST.ProExcision.flatLeftTensorHomologyIso
#print axioms SerrePositivity.KST.ProExcision.flatLeftTensorHomologyIso

#check @SerrePositivity.KST.ProExcision.singleTensorHomologyIso
#print axioms SerrePositivity.KST.ProExcision.singleTensorHomologyIso

#check @SerrePositivity.KST.ProExcision.truncationTensorConeIsoOfEq
#print axioms SerrePositivity.KST.ProExcision.truncationTensorConeIsoOfEq

#check @SerrePositivity.KST.ProExcision.scalarConeTensorIso
#print axioms SerrePositivity.KST.ProExcision.scalarConeTensorIso

#check @SerrePositivity.KST.ProExcision.totalKoszulTensorIso
#print axioms SerrePositivity.KST.ProExcision.totalKoszulTensorIso

#check @SerrePositivity.KST.ProExcision.tensorDegreeMap_apply_homogeneous
#print axioms SerrePositivity.KST.ProExcision.tensorDegreeMap_apply_homogeneous

#check @SerrePositivity.KST.ProExcision.tensorSplitBoundary_apply_homogeneous
#print axioms SerrePositivity.KST.ProExcision.tensorSplitBoundary_apply_homogeneous

#check @SerrePositivity.KST.ProExcision.tensorSplitBoundary_homogeneous
#print axioms SerrePositivity.KST.ProExcision.tensorSplitBoundary_homogeneous

#check @SerrePositivity.KST.ProExcision.tensorSplitBoundary_eq
#print axioms SerrePositivity.KST.ProExcision.tensorSplitBoundary_eq

#check @SerrePositivity.KST.ProExcision.cutoffBoundary_differential
#print axioms SerrePositivity.KST.ProExcision.cutoffBoundary_differential

#check @SerrePositivity.KST.ProExcision.cutoffTensorBoundary_differential
#print axioms SerrePositivity.KST.ProExcision.cutoffTensorBoundary_differential

#check @SerrePositivity.KST.ProExcision.splitBoundary_lift_condition
#print axioms SerrePositivity.KST.ProExcision.splitBoundary_lift_condition

#check @SerrePositivity.KST.ProExcision.splitBoundary_isCycle
#print axioms SerrePositivity.KST.ProExcision.splitBoundary_isCycle

#check @SerrePositivity.KST.ProExcision.splitBoundary_connecting
#print axioms SerrePositivity.KST.ProExcision.splitBoundary_connecting

#check @SerrePositivity.KST.ProExcision.splitBoundary_shiftMap_on_cycle
#print axioms SerrePositivity.KST.ProExcision.splitBoundary_shiftMap_on_cycle

#check @SerrePositivity.KST.ProExcision.splitBoundary_connecting_eq_shiftMap
#print axioms SerrePositivity.KST.ProExcision.splitBoundary_connecting_eq_shiftMap

#check @SerrePositivity.KST.ProExcision.coneConnecting_eq_shortExact
#print axioms SerrePositivity.KST.ProExcision.coneConnecting_eq_shortExact

#check @SerrePositivity.KST.ProExcision.coneCompositeConnecting_quotient
#print axioms SerrePositivity.KST.ProExcision.coneCompositeConnecting_quotient

#check @SerrePositivity.KST.ProExcision.splitBoundary_differential
#print axioms SerrePositivity.KST.ProExcision.splitBoundary_differential

#check @SerrePositivity.KST.ProExcision.splitTensorBoundary_differential
#print axioms SerrePositivity.KST.ProExcision.splitTensorBoundary_differential

#check @SerrePositivity.KST.ProExcision.adjacentCutShortComplex
#print axioms SerrePositivity.KST.ProExcision.adjacentCutShortComplex

#check @SerrePositivity.KST.ProExcision.adjacentCutIso
#print axioms SerrePositivity.KST.ProExcision.adjacentCutIso

#check @SerrePositivity.KST.ProExcision.adjacentCutSplitting
#print axioms SerrePositivity.KST.ProExcision.adjacentCutSplitting

#check @SerrePositivity.KST.ProExcision.adjacentCutShortComplex_shortExact
#print axioms SerrePositivity.KST.ProExcision.adjacentCutShortComplex_shortExact

#check @SerrePositivity.KST.ProExcision.adjacentTensorCutShortComplex
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorCutShortComplex

#check @SerrePositivity.KST.ProExcision.adjacentTensorCutSplitting
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorCutSplitting

#check @SerrePositivity.KST.ProExcision.adjacentTensorCutShortComplex_shortExact
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorCutShortComplex_shortExact

#check @SerrePositivity.KST.ProExcision.truncationInclusion_f_isIso
#print axioms SerrePositivity.KST.ProExcision.truncationInclusion_f_isIso

#check @SerrePositivity.KST.ProExcision.adjacentCutBoundary_differential
#print axioms SerrePositivity.KST.ProExcision.adjacentCutBoundary_differential

#check @SerrePositivity.KST.ProExcision.adjacentTensorCutBoundary_differential
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorCutBoundary_differential

#check @SerrePositivity.KST.ProExcision.intervalCutShortComplex
#print axioms SerrePositivity.KST.ProExcision.intervalCutShortComplex

#check @SerrePositivity.KST.ProExcision.intervalCutIso
#print axioms SerrePositivity.KST.ProExcision.intervalCutIso

#check @SerrePositivity.KST.ProExcision.intervalCutSplitting
#print axioms SerrePositivity.KST.ProExcision.intervalCutSplitting

#check @SerrePositivity.KST.ProExcision.intervalCutShortComplex_shortExact
#print axioms SerrePositivity.KST.ProExcision.intervalCutShortComplex_shortExact

#check @SerrePositivity.KST.ProExcision.intervalTensorCutShortComplex
#print axioms SerrePositivity.KST.ProExcision.intervalTensorCutShortComplex

#check @SerrePositivity.KST.ProExcision.intervalTensorCutSplitting
#print axioms SerrePositivity.KST.ProExcision.intervalTensorCutSplitting

#check @SerrePositivity.KST.ProExcision.intervalTensorCutShortComplex_shortExact
#print axioms SerrePositivity.KST.ProExcision.intervalTensorCutShortComplex_shortExact

#check @SerrePositivity.KST.ProExcision.tensorFiltrationInterval
#print axioms SerrePositivity.KST.ProExcision.tensorFiltrationInterval

#check @SerrePositivity.KST.ProExcision.tensorFiltrationBoundary
#print axioms SerrePositivity.KST.ProExcision.tensorFiltrationBoundary

#check @SerrePositivity.KST.ProExcision.adjacentGradeBoundary
#print axioms SerrePositivity.KST.ProExcision.adjacentGradeBoundary

#check @SerrePositivity.KST.ProExcision.adjacentGradeTermIso
#print axioms SerrePositivity.KST.ProExcision.adjacentGradeTermIso

#check @SerrePositivity.KST.ProExcision.adjacentGradeBoundary_differential
#print axioms SerrePositivity.KST.ProExcision.adjacentGradeBoundary_differential

#check @SerrePositivity.KST.ProExcision.adjacentGrade_isZero_X
#print axioms SerrePositivity.KST.ProExcision.adjacentGrade_isZero_X

#check @SerrePositivity.KST.ProExcision.adjacentGradeIso
#print axioms SerrePositivity.KST.ProExcision.adjacentGradeIso

#check @SerrePositivity.KST.ProExcision.adjacentGradeIso_hom_f
#print axioms SerrePositivity.KST.ProExcision.adjacentGradeIso_hom_f

#check @SerrePositivity.KST.ProExcision.singleDegreeBoundary
#print axioms SerrePositivity.KST.ProExcision.singleDegreeBoundary

#check @SerrePositivity.KST.ProExcision.singleDegreeBoundary_f
#print axioms SerrePositivity.KST.ProExcision.singleDegreeBoundary_f

#check @SerrePositivity.KST.ProExcision.adjacentGradeBoundary_single
#print axioms SerrePositivity.KST.ProExcision.adjacentGradeBoundary_single

#check @SerrePositivity.KST.ProExcision.adjacentTensorGradeBoundary
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorGradeBoundary

#check @SerrePositivity.KST.ProExcision.adjacentTensorGradeBoundary_eq
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorGradeBoundary_eq

#check @SerrePositivity.KST.ProExcision.tensorSingleDegreeBoundary
#print axioms SerrePositivity.KST.ProExcision.tensorSingleDegreeBoundary

#check @SerrePositivity.KST.ProExcision.adjacentTensorGradeBoundary_single
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorGradeBoundary_single

#check @SerrePositivity.KST.ProExcision.flatLeftTensorHomologyIso_coefficient
#print axioms SerrePositivity.KST.ProExcision.flatLeftTensorHomologyIso_coefficient

#check @SerrePositivity.KST.ProExcision.flatLeftTensorHomologyIso_map
#print axioms SerrePositivity.KST.ProExcision.flatLeftTensorHomologyIso_map

#check @SerrePositivity.KST.ProExcision.singleZeroTensorIso_inv_naturality
#print axioms SerrePositivity.KST.ProExcision.singleZeroTensorIso_inv_naturality

#check @SerrePositivity.KST.ProExcision.singleZeroTensorIso_hom_naturality
#print axioms SerrePositivity.KST.ProExcision.singleZeroTensorIso_hom_naturality

#check @SerrePositivity.KST.ProExcision.singleTensorShiftIso_coefficient
#print axioms SerrePositivity.KST.ProExcision.singleTensorShiftIso_coefficient

#check @SerrePositivity.KST.ProExcision.singleTensorHomologyIso_coefficient
#print axioms SerrePositivity.KST.ProExcision.singleTensorHomologyIso_coefficient

#check @SerrePositivity.KST.ProExcision.singleFamilyShift_boundary
#print axioms SerrePositivity.KST.ProExcision.singleFamilyShift_boundary

#check @SerrePositivity.KST.ProExcision.tensorSingleFamily
#print axioms SerrePositivity.KST.ProExcision.tensorSingleFamily

#check @SerrePositivity.KST.ProExcision.tensorSingleDegreeBoundary_id_family
#print axioms SerrePositivity.KST.ProExcision.tensorSingleDegreeBoundary_id_family

#check @SerrePositivity.KST.ProExcision.singleTensorShiftIso_family
#print axioms SerrePositivity.KST.ProExcision.singleTensorShiftIso_family

#check @SerrePositivity.KST.ProExcision.tensorSingleShift_boundary_id
#print axioms SerrePositivity.KST.ProExcision.tensorSingleShift_boundary_id

#check @SerrePositivity.KST.ProExcision.tensorSingleDegreeBoundary_factor
#print axioms SerrePositivity.KST.ProExcision.tensorSingleDegreeBoundary_factor

#check @SerrePositivity.KST.ProExcision.tensorSingleShift_boundary
#print axioms SerrePositivity.KST.ProExcision.tensorSingleShift_boundary

#check @SerrePositivity.KST.ProExcision.shiftMap_comparison
#print axioms SerrePositivity.KST.ProExcision.shiftMap_comparison

#check @SerrePositivity.KST.ProExcision.tensorSingleHomology_shift_boundary
#print axioms SerrePositivity.KST.ProExcision.tensorSingleHomology_shift_boundary

#check @SerrePositivity.KST.ProExcision.tensorSingleHomology_boundary
#print axioms SerrePositivity.KST.ProExcision.tensorSingleHomology_boundary

#check @SerrePositivity.KST.ProExcision.singleTensorHomologyIsoAt
#print axioms SerrePositivity.KST.ProExcision.singleTensorHomologyIsoAt

#check @SerrePositivity.KST.ProExcision.singleTensorHomologyIsoAt_hom
#print axioms SerrePositivity.KST.ProExcision.singleTensorHomologyIsoAt_hom

#check @SerrePositivity.KST.ProExcision.tensorSingleHomology_boundary_at
#print axioms SerrePositivity.KST.ProExcision.tensorSingleHomology_boundary_at

#check @SerrePositivity.KST.ProExcision.adjacentTensorGradeHomologyIso
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorGradeHomologyIso

#check @SerrePositivity.KST.ProExcision.adjacentTensorGradeHomology_differential
#print axioms SerrePositivity.KST.ProExcision.adjacentTensorGradeHomology_differential

#check @SerrePositivity.KST.ProExcision.intervalTensorAdjacentIso
#print axioms SerrePositivity.KST.ProExcision.intervalTensorAdjacentIso

#check @SerrePositivity.KST.ProExcision.intervalTensorGradeBoundary
#print axioms SerrePositivity.KST.ProExcision.intervalTensorGradeBoundary

#check @SerrePositivity.KST.ProExcision.intervalTensorGradeBoundary_adjacent
#print axioms SerrePositivity.KST.ProExcision.intervalTensorGradeBoundary_adjacent

#check @SerrePositivity.KST.ProExcision.intervalTensorGradeHomologyIso
#print axioms SerrePositivity.KST.ProExcision.intervalTensorGradeHomologyIso

#check @SerrePositivity.KST.ProExcision.intervalTensorGradeHomology_differential
#print axioms SerrePositivity.KST.ProExcision.intervalTensorGradeHomology_differential

#check @SerrePositivity.KST.ProExcision.IsProZero.of_natIso
#print axioms SerrePositivity.KST.ProExcision.IsProZero.of_natIso

#check @SerrePositivity.KST.ProExcision.pointwiseTensorSwapIso
#print axioms SerrePositivity.KST.ProExcision.pointwiseTensorSwapIso

#check @SerrePositivity.KST.ProExcision.pointwiseTensorSwapHomologyIso
#print axioms SerrePositivity.KST.ProExcision.pointwiseTensorSwapHomologyIso

#check @SerrePositivity.KST.ProExcision.koszulRightTensorHomologyTower
#print axioms SerrePositivity.KST.ProExcision.koszulRightTensorHomologyTower

#check @SerrePositivity.KST.ProExcision.koszulRightTensorHomologyTower_isProZero
#print axioms SerrePositivity.KST.ProExcision.koszulRightTensorHomologyTower_isProZero

#check @SerrePositivity.KST.ProExcision.leftHomologyModelMap_comm
#print axioms SerrePositivity.KST.ProExcision.leftHomologyModelMap_comm

#check @SerrePositivity.KST.ProExcision.powerKernel
#print axioms SerrePositivity.KST.ProExcision.powerKernel

#check @SerrePositivity.KST.ProExcision.powerKernel_mono
#print axioms SerrePositivity.KST.ProExcision.powerKernel_mono

#check @SerrePositivity.KST.ProExcision.exists_power_torsion_bound
#print axioms SerrePositivity.KST.ProExcision.exists_power_torsion_bound

#check @SerrePositivity.KST.ProExcision.powerKernelTransition
#print axioms SerrePositivity.KST.ProExcision.powerKernelTransition

#check @SerrePositivity.KST.ProExcision.powerKernelTower
#print axioms SerrePositivity.KST.ProExcision.powerKernelTower

#check @SerrePositivity.KST.ProExcision.powerKernelTower_isProZero
#print axioms SerrePositivity.KST.ProExcision.powerKernelTower_isProZero

#check @SerrePositivity.KST.ProExcision.scalarHomologyQuotient
#print axioms SerrePositivity.KST.ProExcision.scalarHomologyQuotient

#check @SerrePositivity.KST.ProExcision.scalarHomologyQuotientπ
#print axioms SerrePositivity.KST.ProExcision.scalarHomologyQuotientπ

#check @SerrePositivity.KST.ProExcision.scalarCone_inr_smul_zero
#print axioms SerrePositivity.KST.ProExcision.scalarCone_inr_smul_zero

#check @SerrePositivity.KST.ProExcision.scalarConeHomologyComparison
#print axioms SerrePositivity.KST.ProExcision.scalarConeHomologyComparison

#check @SerrePositivity.KST.ProExcision.scalarConeHomologyComparison_π
#print axioms SerrePositivity.KST.ProExcision.scalarConeHomologyComparison_π

#check @SerrePositivity.KST.ProExcision.scalarConeHomologyComparison_injective
#print axioms SerrePositivity.KST.ProExcision.scalarConeHomologyComparison_injective

#check @SerrePositivity.KST.ProExcision.scalarConeHomologyComparison_exact
#print axioms SerrePositivity.KST.ProExcision.scalarConeHomologyComparison_exact

#check @SerrePositivity.KST.ProExcision.scalarCone_connecting_smul_zero
#print axioms SerrePositivity.KST.ProExcision.scalarCone_connecting_smul_zero

#check @SerrePositivity.KST.ProExcision.cone_connecting_naturality
#print axioms SerrePositivity.KST.ProExcision.cone_connecting_naturality

#check @SerrePositivity.KST.ProExcision.powerScalarSquare
#print axioms SerrePositivity.KST.ProExcision.powerScalarSquare

#check @SerrePositivity.KST.ProExcision.powerScalarConeMap
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeMap

#check @SerrePositivity.KST.ProExcision.powerScalarConeTower
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeTower

#check @SerrePositivity.KST.ProExcision.powerScalarRange_le
#print axioms SerrePositivity.KST.ProExcision.powerScalarRange_le

#check @SerrePositivity.KST.ProExcision.powerHomologyQuotientTower
#print axioms SerrePositivity.KST.ProExcision.powerHomologyQuotientTower

#check @SerrePositivity.KST.ProExcision.powerScalarConeMap_inr
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeMap_inr

#check @SerrePositivity.KST.ProExcision.powerScalarConeComparison
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeComparison

#check @SerrePositivity.KST.ProExcision.powerScalarConeConnecting
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeConnecting

#check @SerrePositivity.KST.ProExcision.powerScalarConeComparison_isProIso
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeComparison_isProIso

#check @SerrePositivity.KST.ProExcision.coneOfArrowFunctor
#print axioms SerrePositivity.KST.ProExcision.coneOfArrowFunctor

#check @SerrePositivity.KST.ProExcision.BiTower
#print axioms SerrePositivity.KST.ProExcision.BiTower

#check @SerrePositivity.KST.ProExcision.BiTower.row
#print axioms SerrePositivity.KST.ProExcision.BiTower.row

#check @SerrePositivity.KST.ProExcision.BiTower.diagonal
#print axioms SerrePositivity.KST.ProExcision.BiTower.diagonal

#check @SerrePositivity.KST.ProExcision.BiLevelHom
#print axioms SerrePositivity.KST.ProExcision.BiLevelHom

#check @SerrePositivity.KST.ProExcision.BiLevelHom.row
#print axioms SerrePositivity.KST.ProExcision.BiLevelHom.row

#check @SerrePositivity.KST.ProExcision.BiLevelHom.diagonal
#print axioms SerrePositivity.KST.ProExcision.BiLevelHom.diagonal

#check @SerrePositivity.KST.ProExcision.BiLevelHom.diagonal_isProIso
#print axioms SerrePositivity.KST.ProExcision.BiLevelHom.diagonal_isProIso

#check @SerrePositivity.KST.ProExcision.BiTower.diagonal_isProZero
#print axioms SerrePositivity.KST.ProExcision.BiTower.diagonal_isProZero

#check @SerrePositivity.KST.ProExcision.BiTower.map
#print axioms SerrePositivity.KST.ProExcision.BiTower.map

#check @SerrePositivity.KST.ProExcision.IsProZero.of_proIso
#print axioms SerrePositivity.KST.ProExcision.IsProZero.of_proIso

#check @SerrePositivity.KST.ProExcision.scalarCone_homology_finite
#print axioms SerrePositivity.KST.ProExcision.scalarCone_homology_finite

#check @SerrePositivity.KST.ProExcision.koszulComplexOn_homology_finite
#print axioms SerrePositivity.KST.ProExcision.koszulComplexOn_homology_finite

#check @SerrePositivity.KST.ProExcision.scalarQuotientFunctor
#print axioms SerrePositivity.KST.ProExcision.scalarQuotientFunctor

#check @SerrePositivity.KST.ProExcision.scalarConeHomologyComparisonNatTrans
#print axioms SerrePositivity.KST.ProExcision.scalarConeHomologyComparisonNatTrans

#check @SerrePositivity.KST.ProExcision.powerScalarSquare_map
#print axioms SerrePositivity.KST.ProExcision.powerScalarSquare_map

#check @SerrePositivity.KST.ProExcision.powerScalarConeBiTower
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeBiTower

#check @SerrePositivity.KST.ProExcision.powerScalarConeBiTower_row_transition
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeBiTower_row_transition

#check @SerrePositivity.KST.ProExcision.powerScalarRange_map
#print axioms SerrePositivity.KST.ProExcision.powerScalarRange_map

#check @SerrePositivity.KST.ProExcision.powerHomologyQuotientBiTower
#print axioms SerrePositivity.KST.ProExcision.powerHomologyQuotientBiTower

#check @SerrePositivity.KST.ProExcision.powerHomologyQuotientBiTower_row_transition
#print axioms SerrePositivity.KST.ProExcision.powerHomologyQuotientBiTower_row_transition

#check @SerrePositivity.KST.ProExcision.powerScalarConeBiComparison
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeBiComparison

#check @SerrePositivity.KST.ProExcision.powerScalarConeBiComparison_diagonal_isProIso
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeBiComparison_diagonal_isProIso

#check @SerrePositivity.KST.ProExcision.powerQuotientMap
#print axioms SerrePositivity.KST.ProExcision.powerQuotientMap

#check @SerrePositivity.KST.ProExcision.powerQuotientMap_comp
#print axioms SerrePositivity.KST.ProExcision.powerQuotientMap_comp

#check @SerrePositivity.KST.ProExcision.Tower.powerQuotient
#print axioms SerrePositivity.KST.ProExcision.Tower.powerQuotient

#check @SerrePositivity.KST.ProExcision.LevelHom.powerQuotient
#print axioms SerrePositivity.KST.ProExcision.LevelHom.powerQuotient

#check @SerrePositivity.KST.ProExcision.IsProIso.powerQuotient
#print axioms SerrePositivity.KST.ProExcision.IsProIso.powerQuotient

#check @SerrePositivity.KST.ProExcision.diagonalPowerConeComparison
#print axioms SerrePositivity.KST.ProExcision.diagonalPowerConeComparison

#check @SerrePositivity.KST.ProExcision.koszulConeTower
#print axioms SerrePositivity.KST.ProExcision.koszulConeTower

#check @SerrePositivity.KST.ProExcision.koszulConeTower_obj
#print axioms SerrePositivity.KST.ProExcision.koszulConeTower_obj

#check @SerrePositivity.KST.ProExcision.iteratedPowerQuotientTower
#print axioms SerrePositivity.KST.ProExcision.iteratedPowerQuotientTower

#check @SerrePositivity.KST.ProExcision.koszulConeComparison
#print axioms SerrePositivity.KST.ProExcision.koszulConeComparison

#check @SerrePositivity.KST.ProExcision.koszulConeComparison_isProIso
#print axioms SerrePositivity.KST.ProExcision.koszulConeComparison_isProIso

#check @SerrePositivity.KST.ProExcision.scalarQuotientπ
#print axioms SerrePositivity.KST.ProExcision.scalarQuotientπ

#check @SerrePositivity.KST.ProExcision.Tower.powerQuotientProjection
#print axioms SerrePositivity.KST.ProExcision.Tower.powerQuotientProjection

#check @SerrePositivity.KST.ProExcision.iteratedPowerQuotientProjection
#print axioms SerrePositivity.KST.ProExcision.iteratedPowerQuotientProjection

#check @SerrePositivity.KST.ProExcision.iteratedPowerQuotientProjection_surjective
#print axioms SerrePositivity.KST.ProExcision.iteratedPowerQuotientProjection_surjective

#check @SerrePositivity.KST.ProExcision.ker_comp_scalarQuotientπ
#print axioms SerrePositivity.KST.ProExcision.ker_comp_scalarQuotientπ

#check @SerrePositivity.KST.ProExcision.parameterSubmodule
#print axioms SerrePositivity.KST.ProExcision.parameterSubmodule

#check @SerrePositivity.KST.ProExcision.iteratedPowerQuotientProjection_ker
#print axioms SerrePositivity.KST.ProExcision.iteratedPowerQuotientProjection_ker

#check @SerrePositivity.KST.ProExcision.iteratedPowerQuotientTower_isZero_obj
#print axioms SerrePositivity.KST.ProExcision.iteratedPowerQuotientTower_isZero_obj

#check @SerrePositivity.KST.ProExcision.single_homology_finite
#print axioms SerrePositivity.KST.ProExcision.single_homology_finite

#check @SerrePositivity.KST.ProExcision.koszulConeModuleHomologyTower_isProZero
#print axioms SerrePositivity.KST.ProExcision.koszulConeModuleHomologyTower_isProZero

#check @SerrePositivity.KST.ProExcision.parameterSubmodule_le_iff
#print axioms SerrePositivity.KST.ProExcision.parameterSubmodule_le_iff

#check @SerrePositivity.KST.ProExcision.parameterSubmodule_eq_ideal_smul
#print axioms SerrePositivity.KST.ProExcision.parameterSubmodule_eq_ideal_smul

#check @SerrePositivity.KST.ProExcision.iteratedPowerQuotientProjection_ker_ideal
#print axioms SerrePositivity.KST.ProExcision.iteratedPowerQuotientProjection_ker_ideal

#check @SerrePositivity.KST.ProExcision.parameterSubmodule_powers_le
#print axioms SerrePositivity.KST.ProExcision.parameterSubmodule_powers_le

#check @SerrePositivity.KST.ProExcision.parameterIdeal_powers_le
#print axioms SerrePositivity.KST.ProExcision.parameterIdeal_powers_le

#check @SerrePositivity.KST.ProExcision.submoduleQuotientTower
#print axioms SerrePositivity.KST.ProExcision.submoduleQuotientTower

#check @SerrePositivity.KST.ProExcision.parameterQuotientTower
#print axioms SerrePositivity.KST.ProExcision.parameterQuotientTower

#check @SerrePositivity.KST.ProExcision.parameterQuotientIso
#print axioms SerrePositivity.KST.ProExcision.parameterQuotientIso

#check @SerrePositivity.KST.ProExcision.parameterQuotientIso_mk
#print axioms SerrePositivity.KST.ProExcision.parameterQuotientIso_mk

#check @SerrePositivity.KST.ProExcision.parameterQuotientComparison
#print axioms SerrePositivity.KST.ProExcision.parameterQuotientComparison

#check @SerrePositivity.KST.ProExcision.parameterQuotientComparison_isProIso
#print axioms SerrePositivity.KST.ProExcision.parameterQuotientComparison_isProIso

#check @SerrePositivity.KST.ProExcision.koszul_comparison
#print axioms SerrePositivity.KST.ProExcision.koszul_comparison

#check @SerrePositivity.KST.ProExcision.koszul_comparison_isProIso
#print axioms SerrePositivity.KST.ProExcision.koszul_comparison_isProIso

#check @SerrePositivity.KST.ProExcision.powerKernelTower_isProZero_artinRees
#print axioms SerrePositivity.KST.ProExcision.powerKernelTower_isProZero_artinRees

#check @SerrePositivity.KST.ProExcision.powerScalarConeComparison_isProIso_artinRees
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeComparison_isProIso_artinRees

#check @SerrePositivity.KST.ProExcision.powerScalarConeBiComparison_diagonal_isProIso_artinRees
#print axioms SerrePositivity.KST.ProExcision.powerScalarConeBiComparison_diagonal_isProIso_artinRees

#check @SerrePositivity.KST.ProExcision.ActionProduct
#print axioms SerrePositivity.KST.ProExcision.ActionProduct

#check @SerrePositivity.KST.ProExcision.actionProductMonoid
#print axioms SerrePositivity.KST.ProExcision.actionProductMonoid

#check @SerrePositivity.KST.ProExcision.SimplicialMonoidAction.actionStructure
#print axioms SerrePositivity.KST.ProExcision.SimplicialMonoidAction.actionStructure

#check @SerrePositivity.KST.ProExcision.actionProductProjection
#print axioms SerrePositivity.KST.ProExcision.actionProductProjection

#check @SerrePositivity.KST.ProExcision.actionProductSection
#print axioms SerrePositivity.KST.ProExcision.actionProductSection

#check @SerrePositivity.KST.ProExcision.actionProductFiber
#print axioms SerrePositivity.KST.ProExcision.actionProductFiber

#check @SerrePositivity.KST.ProExcision.actionProduct_decomposition
#print axioms SerrePositivity.KST.ProExcision.actionProduct_decomposition

#check @SerrePositivity.KST.ProExcision.actionProductTwist
#print axioms SerrePositivity.KST.ProExcision.actionProductTwist

#check @SerrePositivity.KST.ProExcision.actionProductMap
#print axioms SerrePositivity.KST.ProExcision.actionProductMap

#check @SerrePositivity.KST.ProExcision.actionProductMap_comp
#print axioms SerrePositivity.KST.ProExcision.actionProductMap_comp

#check @SerrePositivity.KST.ProExcision.actionProductTwist_natural
#print axioms SerrePositivity.KST.ProExcision.actionProductTwist_natural

#check @SerrePositivity.KST.ProExcision.SimplicialMonoidAction
#print axioms SerrePositivity.KST.ProExcision.SimplicialMonoidAction

#check @SerrePositivity.KST.ProExcision.simplicialActionProduct
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProduct

#check @SerrePositivity.KST.ProExcision.simplicialActionProductProjection
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductProjection

#check @SerrePositivity.KST.ProExcision.simplicialActionProductSection
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductSection

#check @SerrePositivity.KST.ProExcision.simplicialActionProductTwist
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductTwist

#check @SerrePositivity.KST.ProExcision.simplicialActionMap
#print axioms SerrePositivity.KST.ProExcision.simplicialActionMap

#check @SerrePositivity.KST.ProExcision.actionTranslation
#print axioms SerrePositivity.KST.ProExcision.actionTranslation

#check @SerrePositivity.KST.ProExcision.actionTranslation_one
#print axioms SerrePositivity.KST.ProExcision.actionTranslation_one

#check @SerrePositivity.KST.ProExcision.actionTranslation_comp
#print axioms SerrePositivity.KST.ProExcision.actionTranslation_comp

#check @SerrePositivity.KST.ProExcision.actionTranslationHomotopy
#print axioms SerrePositivity.KST.ProExcision.actionTranslationHomotopy

#check @SerrePositivity.KST.ProExcision.actionTranslationClass
#print axioms SerrePositivity.KST.ProExcision.actionTranslationClass

#check @SerrePositivity.KST.ProExcision.actionTranslation_map_eq
#print axioms SerrePositivity.KST.ProExcision.actionTranslation_map_eq

#check @SerrePositivity.KST.ProExcision.grouplikeActionIso
#print axioms SerrePositivity.KST.ProExcision.grouplikeActionIso

#check @SerrePositivity.KST.ProExcision.actionFamily
#print axioms SerrePositivity.KST.ProExcision.actionFamily

#check @SerrePositivity.KST.ProExcision.actionFamily_const
#print axioms SerrePositivity.KST.ProExcision.actionFamily_const

#check @SerrePositivity.KST.ProExcision.actionFamilyHomotopyMap
#print axioms SerrePositivity.KST.ProExcision.actionFamilyHomotopyMap

#check @SerrePositivity.KST.ProExcision.actionFamilyHomotopy
#print axioms SerrePositivity.KST.ProExcision.actionFamilyHomotopy

#check @SerrePositivity.KST.ProExcision.actionFamily_const_localized_isIso
#print axioms SerrePositivity.KST.ProExcision.actionFamily_const_localized_isIso

#check @SerrePositivity.KST.ProExcision.actionFamily_simplex_localized_isIso
#print axioms SerrePositivity.KST.ProExcision.actionFamily_simplex_localized_isIso

#check @SerrePositivity.KST.ProExcision.ActionDescent.of_iso
#print axioms SerrePositivity.KST.ProExcision.ActionDescent.of_iso

#check @SerrePositivity.KST.ProExcision.ActionDescent.initial
#print axioms SerrePositivity.KST.ProExcision.ActionDescent.initial

#check @SerrePositivity.KST.ProExcision.ActionDescent.coproduct
#print axioms SerrePositivity.KST.ProExcision.ActionDescent.coproduct

#check @SerrePositivity.KST.ProExcision.ActionDescent.pushout
#print axioms SerrePositivity.KST.ProExcision.ActionDescent.pushout

#check @SerrePositivity.KST.ProExcision.ActionDescent.stage_isIso
#print axioms SerrePositivity.KST.ProExcision.ActionDescent.stage_isIso

#check @SerrePositivity.KST.ProExcision.actionFamily_localized_isIso
#print axioms SerrePositivity.KST.ProExcision.actionFamily_localized_isIso

#check @SerrePositivity.KST.ProExcision.simplicialActionProductUnderlyingIso
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductUnderlyingIso

#check @SerrePositivity.KST.ProExcision.simplicialActionProductTwist_underlying
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductTwist_underlying

#check @SerrePositivity.KST.ProExcision.simplicialActionProductTwist_localized_isIso
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductTwist_localized_isIso

#check @SerrePositivity.KST.ProExcision.ActionObject
#print axioms SerrePositivity.KST.ProExcision.ActionObject

#check @SerrePositivity.KST.ProExcision.actionObjectCategory
#print axioms SerrePositivity.KST.ProExcision.actionObjectCategory

#check @SerrePositivity.KST.ProExcision.SimplicialActionHom
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionHom

#check @SerrePositivity.KST.ProExcision.simplicialActionProductMap
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductMap

#check @SerrePositivity.KST.ProExcision.simplicialActionProductSection_map
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductSection_map

#check @SerrePositivity.KST.ProExcision.SimplicialActionHom.trivial
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionHom.trivial

#check @SerrePositivity.KST.ProExcision.simplicialActionProductMap_trivial
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductMap_trivial

#check @SerrePositivity.KST.ProExcision.relativeModule
#print axioms SerrePositivity.KST.ProExcision.relativeModule

#check @SerrePositivity.KST.ProExcision.relativeModuleMap
#print axioms SerrePositivity.KST.ProExcision.relativeModuleMap

#check @SerrePositivity.KST.ProExcision.relativeModuleMap_zero_of_factor
#print axioms SerrePositivity.KST.ProExcision.relativeModuleMap_zero_of_factor

#check @SerrePositivity.KST.ProExcision.relativeModuleMap_eq_of_right_eq
#print axioms SerrePositivity.KST.ProExcision.relativeModuleMap_eq_of_right_eq

#check @SerrePositivity.KST.ProExcision.relativeModuleMap_comp
#print axioms SerrePositivity.KST.ProExcision.relativeModuleMap_comp

#check @SerrePositivity.KST.ProExcision.relativeBarModule
#print axioms SerrePositivity.KST.ProExcision.relativeBarModule

#check @SerrePositivity.KST.ProExcision.relativeBarSection_projection
#print axioms SerrePositivity.KST.ProExcision.relativeBarSection_projection

#check @SerrePositivity.KST.ProExcision.relativeBarSection_injective
#print axioms SerrePositivity.KST.ProExcision.relativeBarSection_injective

#check @SerrePositivity.KST.ProExcision.relativeBarMap_square
#print axioms SerrePositivity.KST.ProExcision.relativeBarMap_square

#check @SerrePositivity.KST.ProExcision.relativeBarMap
#print axioms SerrePositivity.KST.ProExcision.relativeBarMap

#check @SerrePositivity.KST.ProExcision.relativeBarMap_trivial_zero
#print axioms SerrePositivity.KST.ProExcision.relativeBarMap_trivial_zero

#check @SerrePositivity.KST.ProExcision.relativeBarMap_zero_of_absolute_eq_trivial
#print axioms SerrePositivity.KST.ProExcision.relativeBarMap_zero_of_absolute_eq_trivial

#check @SerrePositivity.KST.ProExcision.actionCategoryProjection
#print axioms SerrePositivity.KST.ProExcision.actionCategoryProjection

#check @SerrePositivity.KST.ProExcision.actionCategoryMap
#print axioms SerrePositivity.KST.ProExcision.actionCategoryMap

#check @SerrePositivity.KST.ProExcision.actionCategoryMap_comp
#print axioms SerrePositivity.KST.ProExcision.actionCategoryMap_comp

#check @SerrePositivity.KST.ProExcision.regularActionObjectContraction
#print axioms SerrePositivity.KST.ProExcision.regularActionObjectContraction

#check @SerrePositivity.KST.ProExcision.regularActionObjectNerveContraction
#print axioms SerrePositivity.KST.ProExcision.regularActionObjectNerveContraction

#check @SerrePositivity.KST.ProExcision.simplicialActionCategory
#print axioms SerrePositivity.KST.ProExcision.simplicialActionCategory

#check @SerrePositivity.KST.ProExcision.bisimplicialActionBar
#print axioms SerrePositivity.KST.ProExcision.bisimplicialActionBar

#check @SerrePositivity.KST.ProExcision.actionBar
#print axioms SerrePositivity.KST.ProExcision.actionBar

#check @SerrePositivity.KST.ProExcision.inverseConjugation
#print axioms SerrePositivity.KST.ProExcision.inverseConjugation

#check @SerrePositivity.KST.ProExcision.conjugationFunctor
#print axioms SerrePositivity.KST.ProExcision.conjugationFunctor

#check @SerrePositivity.KST.ProExcision.conjugationNaturalTransformation
#print axioms SerrePositivity.KST.ProExcision.conjugationNaturalTransformation

#check @SerrePositivity.KST.ProExcision.conjugationNerveHomotopy
#print axioms SerrePositivity.KST.ProExcision.conjugationNerveHomotopy

#check @SerrePositivity.KST.ProExcision.inverseConjugation_naturality
#print axioms SerrePositivity.KST.ProExcision.inverseConjugation_naturality

#check @SerrePositivity.KST.ProExcision.conjugationNaturalTransformation_naturality
#print axioms SerrePositivity.KST.ProExcision.conjugationNaturalTransformation_naturality

#check @SerrePositivity.KST.ProExcision.conjugationChainHomotopy
#print axioms SerrePositivity.KST.ProExcision.conjugationChainHomotopy

#check @SerrePositivity.KST.ProExcision.augmentationTestChains
#print axioms SerrePositivity.KST.ProExcision.augmentationTestChains

#check @SerrePositivity.KST.ProExcision.no_homotopy_identity_doubleIdentity
#print axioms SerrePositivity.KST.ProExcision.no_homotopy_identity_doubleIdentity

#check @SerrePositivity.KST.ProExcision.tensorMap_eq_zero_above
#print axioms SerrePositivity.KST.ProExcision.tensorMap_eq_zero_above
#check @SerrePositivity.KST.ProExcision.tensorMap_augmentation_expansion
#print axioms SerrePositivity.KST.ProExcision.tensorMap_augmentation_expansion
#check @SerrePositivity.KST.ProExcision.tensorMap_augmentation_eq_above
#print axioms SerrePositivity.KST.ProExcision.tensorMap_augmentation_eq_above
#check @SerrePositivity.KST.ProExcision.tensorMap_augmentation_eq_low
#print axioms SerrePositivity.KST.ProExcision.tensorMap_augmentation_eq_low

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceHomotopy
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_hom_ext
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_hom_ext
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso_generator
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso_generator
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso_naturality
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorComparison
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorComparison
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy.truncate
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy.truncate
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorHomotopy
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀_projection
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀_projection
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁_projection
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁_projection
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.cancel_augmentation
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.cancel_augmentation
#check @SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy
#print axioms SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso_naturality
#check @SerrePositivity.KST.ProExcision.conjugationInterval_naturality
#print axioms SerrePositivity.KST.ProExcision.conjugationInterval_naturality
#check @SerrePositivity.KST.ProExcision.conjugationNerveHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.conjugationNerveHomotopy_naturality
#check @SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy_naturality
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homologyMap_eq_of_component_eq
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homologyMap_eq_of_component_eq
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.geometricCylinderHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.geometricCylinderHomotopy
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderHomotopy
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.endpointChainHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.endpointChainHomotopy
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.homologyMap_eq
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.homologyMap_eq
#check @SerrePositivity.KST.ProExcision.SimplicialSetAction
#print axioms SerrePositivity.KST.ProExcision.SimplicialSetAction
#check @SerrePositivity.KST.ProExcision.SimplicialSetAction.actionStructure
#print axioms SerrePositivity.KST.ProExcision.SimplicialSetAction.actionStructure
#check @SerrePositivity.KST.ProExcision.simplicialSetActionCategory
#print axioms SerrePositivity.KST.ProExcision.simplicialSetActionCategory
#check @SerrePositivity.KST.ProExcision.bisimplicialSetActionBar
#print axioms SerrePositivity.KST.ProExcision.bisimplicialSetActionBar
#check @SerrePositivity.KST.ProExcision.setActionBar
#print axioms SerrePositivity.KST.ProExcision.setActionBar

#check @SerrePositivity.KST.ProExcision.monoidNerveAction
#print axioms SerrePositivity.KST.ProExcision.monoidNerveAction
#check @SerrePositivity.KST.ProExcision.barSetAction
#print axioms SerrePositivity.KST.ProExcision.barSetAction
#check @SerrePositivity.KST.ProExcision.coefficientActionBar
#print axioms SerrePositivity.KST.ProExcision.coefficientActionBar

#check @SerrePositivity.KST.ProExcision.actionBarTransport
#print axioms SerrePositivity.KST.ProExcision.actionBarTransport
#check @SerrePositivity.KST.ProExcision.actionBarComparison
#print axioms SerrePositivity.KST.ProExcision.actionBarComparison

#check @SerrePositivity.KST.ProExcision.actionObject_comp_val
#print axioms SerrePositivity.KST.ProExcision.actionObject_comp_val
#check @SerrePositivity.KST.ProExcision.actionObject_eqToHom_val
#print axioms SerrePositivity.KST.ProExcision.actionObject_eqToHom_val
#check @SerrePositivity.KST.ProExcision.actionNerveCoordinates
#print axioms SerrePositivity.KST.ProExcision.actionNerveCoordinates
#check @SerrePositivity.KST.ProExcision.actionNerveSimplexWithSource
#print axioms SerrePositivity.KST.ProExcision.actionNerveSimplexWithSource
#check @SerrePositivity.KST.ProExcision.actionNerveCoordinates_injective
#print axioms SerrePositivity.KST.ProExcision.actionNerveCoordinates_injective
#check @SerrePositivity.KST.ProExcision.actionNerveCoordinates_simplex
#print axioms SerrePositivity.KST.ProExcision.actionNerveCoordinates_simplex
#check @SerrePositivity.KST.ProExcision.actionNerveEquiv
#print axioms SerrePositivity.KST.ProExcision.actionNerveEquiv
#check @SerrePositivity.KST.ProExcision.actionNerveCoordinates_map
#print axioms SerrePositivity.KST.ProExcision.actionNerveCoordinates_map
#check @SerrePositivity.KST.ProExcision.setActionBarRowIso
#print axioms SerrePositivity.KST.ProExcision.setActionBarRowIso
#check @SerrePositivity.KST.ProExcision.SimplicialSetActionHom
#print axioms SerrePositivity.KST.ProExcision.SimplicialSetActionHom
#check @SerrePositivity.KST.ProExcision.simplicialSetActionCategoryMap
#print axioms SerrePositivity.KST.ProExcision.simplicialSetActionCategoryMap
#check @SerrePositivity.KST.ProExcision.setActionBarMap
#print axioms SerrePositivity.KST.ProExcision.setActionBarMap
#check @SerrePositivity.KST.ProExcision.SimplicialSetActionHom.id
#print axioms SerrePositivity.KST.ProExcision.SimplicialSetActionHom.id
#check @SerrePositivity.KST.ProExcision.SimplicialSetActionHom.comp
#print axioms SerrePositivity.KST.ProExcision.SimplicialSetActionHom.comp
#check @SerrePositivity.KST.ProExcision.setActionBarMap_id
#print axioms SerrePositivity.KST.ProExcision.setActionBarMap_id
#check @SerrePositivity.KST.ProExcision.setActionBarMap_comp
#print axioms SerrePositivity.KST.ProExcision.setActionBarMap_comp
#check @SerrePositivity.KST.ProExcision.constantSimplicialMonoidAction
#print axioms SerrePositivity.KST.ProExcision.constantSimplicialMonoidAction
#check @SerrePositivity.KST.ProExcision.discreteCoefficientActionBar
#print axioms SerrePositivity.KST.ProExcision.discreteCoefficientActionBar
#check @SerrePositivity.KST.ProExcision.constantMonoidMap
#print axioms SerrePositivity.KST.ProExcision.constantMonoidMap
#check @SerrePositivity.KST.ProExcision.discreteBarSetActionHom
#print axioms SerrePositivity.KST.ProExcision.discreteBarSetActionHom
#check @SerrePositivity.KST.ProExcision.discreteCoefficientActionBarMap
#print axioms SerrePositivity.KST.ProExcision.discreteCoefficientActionBarMap
#check @SerrePositivity.KST.ProExcision.discreteCoefficientActionBarMap_id
#print axioms SerrePositivity.KST.ProExcision.discreteCoefficientActionBarMap_id
#check @SerrePositivity.KST.ProExcision.discreteCoefficientActionBarMap_comp
#print axioms SerrePositivity.KST.ProExcision.discreteCoefficientActionBarMap_comp
#check @SerrePositivity.KST.ProExcision.coefficientBisimplicialBar
#print axioms SerrePositivity.KST.ProExcision.coefficientBisimplicialBar
#check @SerrePositivity.KST.ProExcision.coefficientBisimplicialBarDiagonalIso
#print axioms SerrePositivity.KST.ProExcision.coefficientBisimplicialBarDiagonalIso
#check @SerrePositivity.KST.ProExcision.coefficientBisimplicialBarRowIso
#print axioms SerrePositivity.KST.ProExcision.coefficientBisimplicialBarRowIso
#check @SerrePositivity.KST.ProExcision.constantMonoidBarIso
#print axioms SerrePositivity.KST.ProExcision.constantMonoidBarIso
#check @SerrePositivity.KST.ProExcision.coefficientBisimplicialBarComparisonApp
#print axioms SerrePositivity.KST.ProExcision.coefficientBisimplicialBarComparisonApp
#check @SerrePositivity.KST.ProExcision.coefficientBisimplicialBarComparison
#print axioms SerrePositivity.KST.ProExcision.coefficientBisimplicialBarComparison
#check @SerrePositivity.KST.ProExcision.coefficientBisimplicialBarComparison_diagonal
#print axioms SerrePositivity.KST.ProExcision.coefficientBisimplicialBarComparison_diagonal
#check @SerrePositivity.KST.ProExcision.tupleMonoid
#print axioms SerrePositivity.KST.ProExcision.tupleMonoid
#check @SerrePositivity.KST.ProExcision.tupleMonoidSpaceIso
#print axioms SerrePositivity.KST.ProExcision.tupleMonoidSpaceIso
#check @SerrePositivity.KST.ProExcision.tupleCoordinate
#print axioms SerrePositivity.KST.ProExcision.tupleCoordinate
#check @SerrePositivity.KST.ProExcision.maskedTupleAction
#print axioms SerrePositivity.KST.ProExcision.maskedTupleAction
#check @SerrePositivity.KST.ProExcision.tupleActionStep
#print axioms SerrePositivity.KST.ProExcision.tupleActionStep
#check @SerrePositivity.KST.ProExcision.tupleActionStep_localized_isIso
#print axioms SerrePositivity.KST.ProExcision.tupleActionStep_localized_isIso

#check @SerrePositivity.KST.ProExcision.tuplePrefixProduct
#print axioms SerrePositivity.KST.ProExcision.tuplePrefixProduct
#check @SerrePositivity.KST.ProExcision.tupleActionSweep
#print axioms SerrePositivity.KST.ProExcision.tupleActionSweep
#check @SerrePositivity.KST.ProExcision.tupleActionSweep_localized_isIso
#print axioms SerrePositivity.KST.ProExcision.tupleActionSweep_localized_isIso
#check @SerrePositivity.KST.ProExcision.tupleActionSweep_base
#print axioms SerrePositivity.KST.ProExcision.tupleActionSweep_base
#check @SerrePositivity.KST.ProExcision.tupleActionSweep_fiber
#print axioms SerrePositivity.KST.ProExcision.tupleActionSweep_fiber
#check @SerrePositivity.KST.ProExcision.monoidNerve_prefix_eq
#print axioms SerrePositivity.KST.ProExcision.monoidNerve_prefix_eq
#check @SerrePositivity.KST.ProExcision.coefficientRowProductIso
#print axioms SerrePositivity.KST.ProExcision.coefficientRowProductIso
#check @SerrePositivity.KST.ProExcision.tupleActionProductUnderlyingIso
#print axioms SerrePositivity.KST.ProExcision.tupleActionProductUnderlyingIso
#check @SerrePositivity.KST.ProExcision.semidirectBarRowProductIso
#print axioms SerrePositivity.KST.ProExcision.semidirectBarRowProductIso
#check @SerrePositivity.KST.ProExcision.coefficientBarRowComparison
#print axioms SerrePositivity.KST.ProExcision.coefficientBarRowComparison
#check @SerrePositivity.KST.ProExcision.coefficientBarRowComparison_eq_sweep
#print axioms SerrePositivity.KST.ProExcision.coefficientBarRowComparison_eq_sweep
#check @SerrePositivity.KST.ProExcision.coefficientBarRowComparison_localized_isIso
#print axioms SerrePositivity.KST.ProExcision.coefficientBarRowComparison_localized_isIso
#check @SerrePositivity.KST.ProExcision.bisimplicialDiagonalFlipIso
#print axioms SerrePositivity.KST.ProExcision.bisimplicialDiagonalFlipIso
#check @SerrePositivity.KST.ProExcision.bisimplicialDiagonalFlipIso_naturality
#print axioms SerrePositivity.KST.ProExcision.bisimplicialDiagonalFlipIso_naturality
#check @SerrePositivity.KST.ProExcision.localized_diagonal_map_of_flipped_rows
#print axioms SerrePositivity.KST.ProExcision.localized_diagonal_map_of_flipped_rows
#check @SerrePositivity.KST.ProExcision.actionBarComparison_localized_isIso
#print axioms SerrePositivity.KST.ProExcision.actionBarComparison_localized_isIso
#check @SerrePositivity.KST.ProExcision.propA1LocalizedComparisonIso
#print axioms SerrePositivity.KST.ProExcision.propA1LocalizedComparisonIso
#check @SerrePositivity.KST.ProExcision.actionBarComparison_map_isIso
#print axioms SerrePositivity.KST.ProExcision.actionBarComparison_map_isIso
#check @SerrePositivity.KST.ProExcision.propA1ComparisonIso
#print axioms SerrePositivity.KST.ProExcision.propA1ComparisonIso
#check @SerrePositivity.KST.ProExcision.barSetActionHom
#print axioms SerrePositivity.KST.ProExcision.barSetActionHom
#check @SerrePositivity.KST.ProExcision.coefficientActionBarMap
#print axioms SerrePositivity.KST.ProExcision.coefficientActionBarMap
#check @SerrePositivity.KST.ProExcision.actionBarComparison_naturality
#print axioms SerrePositivity.KST.ProExcision.actionBarComparison_naturality
#check @SerrePositivity.KST.ProExcision.propA1ComparisonIso_naturality
#print axioms SerrePositivity.KST.ProExcision.propA1ComparisonIso_naturality

#check @SerrePositivity.KST.ProExcision.actionNerveWordCoordinates
#print axioms SerrePositivity.KST.ProExcision.actionNerveWordCoordinates
#check @SerrePositivity.KST.ProExcision.actionNerveWordCoordinates_injective
#print axioms SerrePositivity.KST.ProExcision.actionNerveWordCoordinates_injective
#check @SerrePositivity.KST.ProExcision.actionNerveWordEquiv
#print axioms SerrePositivity.KST.ProExcision.actionNerveWordEquiv
#check @SerrePositivity.KST.ProExcision.actionNerveWordSection
#print axioms SerrePositivity.KST.ProExcision.actionNerveWordSection
#check @SerrePositivity.KST.ProExcision.actionNerveWordSection_source
#print axioms SerrePositivity.KST.ProExcision.actionNerveWordSection_source
#check @SerrePositivity.KST.ProExcision.actionNerveWordSection_projection
#print axioms SerrePositivity.KST.ProExcision.actionNerveWordSection_projection
#check @SerrePositivity.KST.ProExcision.setActionBarProjection
#print axioms SerrePositivity.KST.ProExcision.setActionBarProjection
#check @SerrePositivity.KST.ProExcision.setActionBarFiberSection
#print axioms SerrePositivity.KST.ProExcision.setActionBarFiberSection
#check @SerrePositivity.KST.ProExcision.setActionBarFiberSection_projection
#print axioms SerrePositivity.KST.ProExcision.setActionBarFiberSection_projection
#check @SerrePositivity.KST.ProExcision.setActionBarFiberSection_source
#print axioms SerrePositivity.KST.ProExcision.setActionBarFiberSection_source
#check @SerrePositivity.KST.ProExcision.barWordFacePrefix
#print axioms SerrePositivity.KST.ProExcision.barWordFacePrefix
#check @SerrePositivity.KST.ProExcision.setActionBarFiberSection_naturality
#print axioms SerrePositivity.KST.ProExcision.setActionBarFiberSection_naturality
#check @SerrePositivity.KST.ProExcision.setActionBarFiberSection_reconstruct
#print axioms SerrePositivity.KST.ProExcision.setActionBarFiberSection_reconstruct
#check @SerrePositivity.KST.ProExcision.setActionBar_map_source
#print axioms SerrePositivity.KST.ProExcision.setActionBar_map_source
#check @SerrePositivity.KST.ProExcision.setActionBar_map_projection
#print axioms SerrePositivity.KST.ProExcision.setActionBar_map_projection
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator
#check @SerrePositivity.KST.ProExcision.linearizedSetAction
#print axioms SerrePositivity.KST.ProExcision.linearizedSetAction
#check @SerrePositivity.KST.ProExcision.linearizedActionBarFiber
#print axioms SerrePositivity.KST.ProExcision.linearizedActionBarFiber
#check @SerrePositivity.KST.ProExcision.linearizedActionBarFiber_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedActionBarFiber_naturality

#check @SerrePositivity.KST.ProExcision.EquivariantLinearizedCylinderMap
#print axioms SerrePositivity.KST.ProExcision.EquivariantLinearizedCylinderMap
#check @SerrePositivity.KST.ProExcision.linearizedActionBarCylinderApp
#print axioms SerrePositivity.KST.ProExcision.linearizedActionBarCylinderApp
#check @SerrePositivity.KST.ProExcision.linearizedActionBarCylinderApp_generator
#print axioms SerrePositivity.KST.ProExcision.linearizedActionBarCylinderApp_generator
#check @SerrePositivity.KST.ProExcision.linearizedActionBarCylinderMap
#print axioms SerrePositivity.KST.ProExcision.linearizedActionBarCylinderMap

#check @SerrePositivity.KST.ProExcision.integerTensorIso_inv_generator
#print axioms SerrePositivity.KST.ProExcision.integerTensorIso_inv_generator
#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₀_generator
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₀_generator
#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₁_generator
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₁_generator
#check @SerrePositivity.KST.ProExcision.setActionBarMap_projection
#print axioms SerrePositivity.KST.ProExcision.setActionBarMap_projection
#check @SerrePositivity.KST.ProExcision.setActionBarFiberSection_map
#print axioms SerrePositivity.KST.ProExcision.setActionBarFiberSection_map
#check @SerrePositivity.KST.ProExcision.linearizedActionBarCylinder_endpoint_generator
#print axioms SerrePositivity.KST.ProExcision.linearizedActionBarCylinder_endpoint_generator
#check @SerrePositivity.KST.ProExcision.linearizedActionBarMHomotopy
#print axioms SerrePositivity.KST.ProExcision.linearizedActionBarMHomotopy
#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel
#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel.map_eq_of_mHomotopy
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel.map_eq_of_mHomotopy
#check @SerrePositivity.KST.ProExcision.HomologicallyMConstant
#print axioms SerrePositivity.KST.ProExcision.HomologicallyMConstant
#check @SerrePositivity.KST.ProExcision.lemmaA4_absolute
#print axioms SerrePositivity.KST.ProExcision.lemmaA4_absolute
#check @SerrePositivity.KST.ProExcision.lemmaA4
#print axioms SerrePositivity.KST.ProExcision.lemmaA4

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.strictifiedMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.strictifiedMap
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.strictifiedMap_eq_low
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.strictifiedMap_eq_low
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.strictifiedDifference_eq_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.strictifiedDifference_eq_zero
#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.strictificationHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.strictificationHomotopy
#check @SerrePositivity.KST.ProExcision.obstructionDihedral
#print axioms SerrePositivity.KST.ProExcision.obstructionDihedral
#check @SerrePositivity.KST.ProExcision.obstructionRotation
#print axioms SerrePositivity.KST.ProExcision.obstructionRotation
#check @SerrePositivity.KST.ProExcision.obstructionReflection
#print axioms SerrePositivity.KST.ProExcision.obstructionReflection
#check @SerrePositivity.KST.ProExcision.obstructionHalfTurn
#print axioms SerrePositivity.KST.ProExcision.obstructionHalfTurn
#check @SerrePositivity.KST.ProExcision.dihedralExponent
#print axioms SerrePositivity.KST.ProExcision.dihedralExponent
#check @SerrePositivity.KST.ProExcision.dihedralCarryCocycle
#print axioms SerrePositivity.KST.ProExcision.dihedralCarryCocycle
#check @SerrePositivity.KST.ProExcision.dihedralCarryCocycle_law
#print axioms SerrePositivity.KST.ProExcision.dihedralCarryCocycle_law
#check @SerrePositivity.KST.ProExcision.dihedralCarryCocycle_normalized
#print axioms SerrePositivity.KST.ProExcision.dihedralCarryCocycle_normalized
#check @SerrePositivity.KST.ProExcision.obstructionHalfTurn_commute
#print axioms SerrePositivity.KST.ProExcision.obstructionHalfTurn_commute
#check @SerrePositivity.KST.ProExcision.obstructionHalfTurn_commutator
#print axioms SerrePositivity.KST.ProExcision.obstructionHalfTurn_commutator
#check @SerrePositivity.KST.ProExcision.obstructionBarBoundary₂
#print axioms SerrePositivity.KST.ProExcision.obstructionBarBoundary₂
#check @SerrePositivity.KST.ProExcision.obstructionTorusCycle
#print axioms SerrePositivity.KST.ProExcision.obstructionTorusCycle
#check @SerrePositivity.KST.ProExcision.obstructionTorusCycle_boundary
#print axioms SerrePositivity.KST.ProExcision.obstructionTorusCycle_boundary
#check @SerrePositivity.KST.ProExcision.obstructionBarBoundary₃
#print axioms SerrePositivity.KST.ProExcision.obstructionBarBoundary₃
#check @SerrePositivity.KST.ProExcision.obstructionCocycleEvaluation
#print axioms SerrePositivity.KST.ProExcision.obstructionCocycleEvaluation
#check @SerrePositivity.KST.ProExcision.obstructionCocycleEvaluation_boundary
#print axioms SerrePositivity.KST.ProExcision.obstructionCocycleEvaluation_boundary
#check @SerrePositivity.KST.ProExcision.obstructionCocycleEvaluation_torus
#print axioms SerrePositivity.KST.ProExcision.obstructionCocycleEvaluation_torus
#check @SerrePositivity.KST.ProExcision.obstructionTorusCycle_not_boundary
#print axioms SerrePositivity.KST.ProExcision.obstructionTorusCycle_not_boundary
#check @SerrePositivity.KST.ProExcision.obstructionHalfTurnBoundingChain
#print axioms SerrePositivity.KST.ProExcision.obstructionHalfTurnBoundingChain
#check @SerrePositivity.KST.ProExcision.obstructionHalfTurnBoundingChain_boundary
#print axioms SerrePositivity.KST.ProExcision.obstructionHalfTurnBoundingChain_boundary

#check @SerrePositivity.KST.ProExcision.LinearizedEquivariant
#print axioms SerrePositivity.KST.ProExcision.LinearizedEquivariant

#check @SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant
#print axioms SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant

#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₀_equivariant
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₀_equivariant

#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₁_equivariant
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₁_equivariant

#check @SerrePositivity.KST.ProExcision.linearizedCylinderProjection_equivariant
#print axioms SerrePositivity.KST.ProExcision.linearizedCylinderProjection_equivariant

#check @SerrePositivity.KST.ProExcision.LinearizedEquivariant.add
#print axioms SerrePositivity.KST.ProExcision.LinearizedEquivariant.add

#check @SerrePositivity.KST.ProExcision.LinearizedEquivariant.sub
#print axioms SerrePositivity.KST.ProExcision.LinearizedEquivariant.sub

#check @SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.endpoint₀
#print axioms SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.endpoint₀

#check @SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.endpoint₁
#print axioms SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.endpoint₁

#check @SerrePositivity.KST.ProExcision.LinearizedEquivariant.constant
#print axioms SerrePositivity.KST.ProExcision.LinearizedEquivariant.constant

#check @SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.add
#print axioms SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.add

#check @SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.sub
#print axioms SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.sub

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictifiedMap_equivariant
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictifiedMap_equivariant

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictificationHomotopy_equivariant
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictificationHomotopy_equivariant

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.cancel_augmentation_equivariant
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.cancel_augmentation_equivariant

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedMap_component_eq
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedMap_component_eq

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedMap_eq_retract
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedMap_eq_retract

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedChainHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedChainHomotopy

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.normalized_strictifiedMap_eq_low
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.normalized_strictifiedMap_eq_low

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.normalized_strictifiedDifference_eq_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.normalized_strictifiedDifference_eq_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.normalizedStrictificationHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy.normalizedStrictificationHomotopy

#check @SerrePositivity.KST.ProExcision.GroupProductData
#print axioms SerrePositivity.KST.ProExcision.GroupProductData

#check @SerrePositivity.KST.ProExcision.GroupProductData.left
#print axioms SerrePositivity.KST.ProExcision.GroupProductData.left

#check @SerrePositivity.KST.ProExcision.GroupProductData.right
#print axioms SerrePositivity.KST.ProExcision.GroupProductData.right

#check @SerrePositivity.KST.ProExcision.GroupProductData.product
#print axioms SerrePositivity.KST.ProExcision.GroupProductData.product

#check @SerrePositivity.KST.ProExcision.GroupProductData.product_apply
#print axioms SerrePositivity.KST.ProExcision.GroupProductData.product_apply

#check @SerrePositivity.KST.ProExcision.GroupProductData.images_commute
#print axioms SerrePositivity.KST.ProExcision.GroupProductData.images_commute

#check @SerrePositivity.KST.ProExcision.groupLinearizedMap
#print axioms SerrePositivity.KST.ProExcision.groupLinearizedMap

#check @SerrePositivity.KST.ProExcision.discreteNerveAction
#print axioms SerrePositivity.KST.ProExcision.discreteNerveAction

#check @SerrePositivity.KST.ProExcision.EquivariantGroupProductData
#print axioms SerrePositivity.KST.ProExcision.EquivariantGroupProductData

#check @SerrePositivity.KST.ProExcision.ConstructionA5Input
#print axioms SerrePositivity.KST.ProExcision.ConstructionA5Input

#check @SerrePositivity.KST.ProExcision.groupLinearizedMap_equivariant
#print axioms SerrePositivity.KST.ProExcision.groupLinearizedMap_equivariant

#check @SerrePositivity.KST.ProExcision.EquivariantGroupProductData.left_equivariant
#print axioms SerrePositivity.KST.ProExcision.EquivariantGroupProductData.left_equivariant

#check @SerrePositivity.KST.ProExcision.EquivariantGroupProductData.right_equivariant
#print axioms SerrePositivity.KST.ProExcision.EquivariantGroupProductData.right_equivariant

#check @SerrePositivity.KST.ProExcision.EquivariantGroupProductData.product_equivariant
#print axioms SerrePositivity.KST.ProExcision.EquivariantGroupProductData.product_equivariant

#check @SerrePositivity.KST.ProExcision.ConstructionA5Input.first_strictified_equivariant
#print axioms SerrePositivity.KST.ProExcision.ConstructionA5Input.first_strictified_equivariant

#check @SerrePositivity.KST.ProExcision.ConstructionA5Input.second_strictified_equivariant
#print axioms SerrePositivity.KST.ProExcision.ConstructionA5Input.second_strictified_equivariant

#check @SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy_equivariant
#print axioms SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy_equivariant

#check @SerrePositivity.KST.ProExcision.conjugationEquivariantCylinderMap
#print axioms SerrePositivity.KST.ProExcision.conjugationEquivariantCylinderMap

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_id
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_id

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_add_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_add_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_add_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_add_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorRight
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorRight

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorRight_additive
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorRight_additive

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor_additive
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor_additive

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor_obj_additive
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor_obj_additive

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor_hasTotal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor_hasTotal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_eq_zero_low
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_eq_zero_low

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_sub_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_sub_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_sub_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_sub_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_augmentation_expansion
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_augmentation_expansion

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_augmentation_eq_low
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_augmentation_eq_low

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedStrictifiedTensor_eq_low
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedStrictifiedTensor_eq_low

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.refl
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.refl

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.symm
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.symm

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.trans
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.trans

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.restrict
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.restrict

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.postcomp
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.postcomp

#check @SerrePositivity.KST.ProExcision.linearizedCylinderMap
#print axioms SerrePositivity.KST.ProExcision.linearizedCylinderMap

#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₀_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₀_naturality

#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₁_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₁_naturality

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.precomp
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.precomp

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront_apply
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront_apply

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack_apply
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack_apply

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDegrees
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDegrees

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_apply
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_apply

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFace_apply
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFace_apply

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_before
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_before

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_after
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_after

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_inside
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_inside

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront_eq_interval
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront_eq_interval

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack_eq_interval
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack_eq_interval

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWLeftIndex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWLeftIndex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWRightIndex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWRightIndex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryIndexForward
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryIndexForward

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryIndexInverse
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryIndexInverse

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryIndexEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryIndexEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryIndex_sum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryIndex_sum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_zero_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_zero_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_zero_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_zero_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMapLeftAddHom
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMapLeftAddHom

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMapRightAddHom
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMapRightAddHom

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_sum_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_sum_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_sum_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_sum_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_zsmul_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_zsmul_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_zsmul_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_zsmul_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_D₁
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_D₁

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_D₂
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_D₂

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_zero_D₁
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_zero_D₁

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_zero_D₂
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_zero_D₂

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_source_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_source_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_last
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_last

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval_face_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDiagonal_sign_cancel
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDiagonal_sign_cancel

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_source_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_source_boundary

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_interval_congr
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_interval_congr

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand_succ_D₁
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand_succ_D₁

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_horizontal_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_horizontal_boundary

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand_castSucc_D₂
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand_castSucc_D₂

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_vertical_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_vertical_boundary

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awLeftBoundaryCoordinates
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awLeftBoundaryCoordinates

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awRightBoundaryCoordinates
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awRightBoundaryCoordinates

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awLeftBoundaryTerm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awLeftBoundaryTerm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awRightBoundaryTerm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awRightBoundaryTerm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDiagonalBoundaryTerm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDiagonalBoundaryTerm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryCoordinates_sum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryCoordinates_sum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontalFaceTerm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontalFaceTerm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVerticalFaceTerm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVerticalFaceTerm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDeletedFaceTerm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDeletedFaceTerm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awCutDiagonalTerm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awCutDiagonalTerm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontalFaceTerm_eq
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontalFaceTerm_eq

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontalFaceTerm_nonDiagonal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontalFaceTerm_nonDiagonal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVerticalFaceTerm_nonDiagonal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVerticalFaceTerm_nonDiagonal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontalFaceTerm_diagonal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontalFaceTerm_diagonal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVerticalFaceTerm_diagonal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVerticalFaceTerm_diagonal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontal_boundary_model
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontal_boundary_model

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVertical_boundary_model
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVertical_boundary_model

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontal_sum_split
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awHorizontal_sum_split

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVertical_sum_split
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awVertical_sum_split

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_comm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_comm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_comp
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_comp

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.compl_card
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.compl_card

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_apply
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_apply

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_apply
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_apply

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleApp
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleApp

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_shuffleApp
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_shuffleApp

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleApp_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleApp_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shufflePrefix_card
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shufflePrefix_card

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shufflePrefix_partition
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shufflePrefix_partition

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.coordinates_add
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.coordinates_add

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_last
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_last

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_last
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_last

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shufflePrefix_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shufflePrefix_succ

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_step
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_step

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_step
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_step

#check @SerrePositivity.KST.ProExcision.discretePath_intermediate
#print axioms SerrePositivity.KST.ProExcision.discretePath_intermediate

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.left_surjective
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.left_surjective

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.right_surjective
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.right_surjective

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_left_prefix
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_left_prefix

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_right_prefix
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_right_prefix

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixedFaceVertex_ne
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixedFaceVertex_ne

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_left_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_left_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_right_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_right_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleSwapMixedFace_map
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleSwapMixedFace_map

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.mem_swapSteps
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.mem_swapSteps

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_swapSteps
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_swapSteps

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions_eq_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions_eq_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_inversions
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_inversions

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_sign
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.swapSteps_sign

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleSwapMixedFace_cancel
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleSwapMixedFace_cancel

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_not_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_not_mem

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_mem

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_not_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_not_mem

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_mem_image
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_mem_image

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_mem_image
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_mem_image

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_prefix_compare
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_prefix_compare

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_prefix_card
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_prefix_card

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_vertex_val
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_vertex_val

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_vertex_after
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_vertex_after

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.discretePath_threshold
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.discretePath_threshold

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_threshold
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_threshold

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_threshold
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right_threshold

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_left_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_left_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_right_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_right_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_left_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_left_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_right_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_right_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_zero_prefix_card
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_zero_prefix_card

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_zero_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_zero_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_zero_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_zero_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_zero_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_zero_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_zero_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_zero_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_first_left_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_first_left_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_first_right_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_first_right_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_first_left_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_first_left_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_first_right_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_first_right_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_last_left_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_last_left_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_last_right_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_last_right_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_last_left_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_last_left_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_last_right_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_last_right_face

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_compl
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_compl

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_right_image
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_right_image

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_right_insert
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_right_insert

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_inversions
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_inversions

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_face_sign
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_face_sign

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_step_val
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInsertion_step_val

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_left_image
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_left_image

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_right_image
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_right_image

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.suffix_card
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.suffix_card

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_inversions
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_inversions

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_face_sign
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_face_sign

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeHorizontal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeHorizontal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeVertical
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeVertical

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeHorizontal_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeHorizontal_mem

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeVertical_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeVertical_mem

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeHorizontal_insertHorizontal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeHorizontal_insertHorizontal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeVertical_insertVertical
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.removeVertical_insertVertical

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_removeHorizontal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertHorizontal_removeHorizontal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_removeVertical
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.insertVertical_removeVertical

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalInsertionEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalInsertionEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalInsertionEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalInsertionEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.rank_eq_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.rank_eq_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalStep
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalStep

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalStep_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalStep_mem

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalStep_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalStep_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalFaceInteriorRank
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalFaceInteriorRank

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFacePosition
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFacePosition

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFaceVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFaceVertex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFaceInterior_coface
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFaceInterior_coface

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose_transpose
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose_transpose

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose_insertVertical
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.transpose_insertVertical

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFacePosition
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFacePosition

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFaceVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFaceVertex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFace_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFace_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFace_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFace_right

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MixedShuffleIndex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MixedShuffleIndex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MixedShuffleIndex.swap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MixedShuffleIndex.swap

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MixedShuffleIndex.swap_swap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MixedShuffleIndex.swap_swap

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MixedShuffleIndex.swap_ne_self
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MixedShuffleIndex.swap_ne_self

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixedWeight
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixedWeight

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixedWeight_cancel_of_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixedWeight_cancel_of_left

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixedWeight_cancel
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixedWeight_cancel

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixed_sum_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleMixed_sum_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalStep_eq_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalStep_eq_iff

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_lt_of_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left_lt_of_mem

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_internal_coordinates
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_internal_coordinates

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_coface
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_coface

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IsHorizontalShuffleFace
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IsHorizontalShuffleFace

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_isHorizontal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_isHorizontal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryRemovalPosition
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryRemovalPosition

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryRemovalPosition_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryRemovalPosition_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryRemovalPosition_last
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryRemovalPosition_last

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryRemovalPosition_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryRemovalPosition_succ

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_removalPosition
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_removalPosition

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleFace_prev_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleFace_prev_mem

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_last_coordinates
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_last_coordinates

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleBoundary_recover
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleBoundary_recover

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HorizontalShuffleBoundaryIndex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HorizontalShuffleBoundaryIndex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleBoundaryEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleBoundaryEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleFace_decidable
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleFace_decidable

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleBoundary_sum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleBoundary_sum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleTransposeEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleTransposeEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.VerticalShuffleBoundaryIndex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.VerticalShuffleBoundaryIndex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalBoundaryTransposeEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalBoundaryTransposeEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleBoundaryEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleBoundaryEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleBoundaryEquiv_apply
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleBoundaryEquiv_apply

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleBoundary_sum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleBoundary_sum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleFace_map
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleFace_map

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleFace_map
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleFace_map

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_sign
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.horizontalFace_sign

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFace_sign
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.verticalFace_sign

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleWeight
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleWeight

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleWeight
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleWeight

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleWeight_equiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffleWeight_equiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleWeight_equiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleWeight_equiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffle_sum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontalShuffle_sum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffle_sum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffle_sum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IsUniformShuffleFace
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IsUniformShuffleFace

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.uniformShuffleFace_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.uniformShuffleFace_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.uniformShuffleFace_last
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.uniformShuffleFace_last

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.uniformShuffleFace_internal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.uniformShuffleFace_internal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IsVerticalShuffleFace
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IsVerticalShuffleFace

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleFace_decidable
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleFace_decidable

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontal_vertical_shuffleFace_disjoint
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.horizontal_vertical_shuffleFace_disjoint

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleFace_not_pure_endpoints
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleFace_not_pure_endpoints

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInternalVertex_eq
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleInternalVertex_eq

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleFace_not_pure_mixed
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleFace_not_pure_mixed

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AllHorizontalShuffleBoundaryIndex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AllHorizontalShuffleBoundaryIndex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AllVerticalShuffleBoundaryIndex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AllVerticalShuffleBoundaryIndex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AllMixedShuffleBoundaryIndex
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AllMixedShuffleBoundaryIndex

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mixedShuffleFace_not_pure
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mixedShuffleFace_not_pure

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryPartitionEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryPartitionEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryPartition_sum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryPartition_sum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryWeight
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundaryWeight

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_mixed_sum_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_mixed_sum_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree_boundary

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree_boundary_pure
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree_boundary_pure

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleFace_iff_transpose
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.verticalShuffleFace_iff_transpose

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.allVerticalShuffleBoundaryEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.allVerticalShuffleBoundaryEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleFace_not_horizontal_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleFace_not_horizontal_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleFace_not_vertical_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleFace_not_vertical_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_horizontal_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_horizontal_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_vertical_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_vertical_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_horizontal_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_horizontal_succ

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_vertical_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBoundary_vertical_succ

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle_horizontal_differential
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle_horizontal_differential

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle_vertical_differential
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle_vertical_differential

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle_comm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle_comm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairModel
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairModel

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.augmentedSimplexPairModel
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.augmentedSimplexPairModel

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairExtraDegeneracy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairExtraDegeneracy

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairModelMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairModelMap

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedAugmentedSimplexPairModel
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedAugmentedSimplexPairModel

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairLinearExtraDegeneracy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairLinearExtraDegeneracy

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.extraDegeneracy_positive_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.extraDegeneracy_positive_boundary

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.extraDegeneracy_fill_cycle
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.extraDegeneracy_fill_cycle

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluationApp
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluationApp

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluationApp_generator
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluationApp_generator

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation_map_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation_map_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_generator
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_generator

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_tmul
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_tmul

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_pure_hom_ext
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_pure_hom_ext

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation_modelMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation_modelMap

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_modelMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_modelMap

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_map_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_map_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_boundary

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairUniversalDiagonal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairUniversalDiagonal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_universalDiagonal
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_universalDiagonal

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluationRetraction
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluationRetraction

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation_retraction
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairEvaluation_retraction

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_injective
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_injective

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalComposite
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalComposite

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_ezComposite
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_ezComposite

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalDifference
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalDifference

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_ezDifference
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_ezDifference

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum_sub
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum_sub

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_faceSum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairOperation_faceSum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum_faceSum
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum_faceSum

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPairFaceSum_boundary

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezDifference_comm
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezDifference_comm

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalDifference_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalDifference_boundary

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezComposite_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezComposite_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalDifference_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalDifference_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPair_fill_cycle
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexPair_fill_cycle

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalHomotopyChain
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalHomotopyChain

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalHomotopyChain_boundary_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalHomotopyChain_boundary_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalHomotopyChain_boundary_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezUniversalHomotopyChain_boundary_succ

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopyApp
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopyApp

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopyApp_boundary_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopyApp_boundary_zero

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopyApp_boundary_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopyApp_boundary_succ

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopy

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopyApp_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ezHomotopyApp_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_id
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap_id

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorHomotopy

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMooreRetraction
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMooreRetraction

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedEZRawHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedEZRawHomotopy

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedEZInsertMooreHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedEZInsertMooreHomotopy

#check @SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedEZHomotopy
#print axioms SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedEZHomotopy

#check @SerrePositivity.KST.ProExcision.mooreHsigmaHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.mooreHsigmaHomotopy_naturality

#check @SerrePositivity.KST.ProExcision.mooreFiniteHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.mooreFiniteHomotopy_naturality

#check @SerrePositivity.KST.ProExcision.moorePInftyHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.moorePInftyHomotopy_naturality

#check @SerrePositivity.KST.ProExcision.ι_chainIntegerTensorHomotopy
#print axioms SerrePositivity.KST.ProExcision.ι_chainIntegerTensorHomotopy

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorHomotopyToId_naturality
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorHomotopyToId_naturality

#check @SerrePositivity.KST.ProExcision.mooreRetractionHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.mooreRetractionHomotopy_naturality

#check @SerrePositivity.KST.ProExcision.mooreProjectionRetraction_naturality
#print axioms SerrePositivity.KST.ProExcision.mooreProjectionRetraction_naturality

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorMooreRetraction_naturality
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorMooreRetraction_naturality

#check @SerrePositivity.KST.ProExcision.ChainHomotopySquare
#print axioms SerrePositivity.KST.ProExcision.ChainHomotopySquare

#check @SerrePositivity.KST.ProExcision.ChainHomotopySquare.ofEq
#print axioms SerrePositivity.KST.ProExcision.ChainHomotopySquare.ofEq

#check @SerrePositivity.KST.ProExcision.ChainHomotopySquare.trans
#print axioms SerrePositivity.KST.ProExcision.ChainHomotopySquare.trans

#check @SerrePositivity.KST.ProExcision.ChainHomotopySquare.symm
#print axioms SerrePositivity.KST.ProExcision.ChainHomotopySquare.symm

#check @SerrePositivity.KST.ProExcision.ChainHomotopySquare.compLeft
#print axioms SerrePositivity.KST.ProExcision.ChainHomotopySquare.compLeft

#check @SerrePositivity.KST.ProExcision.ChainHomotopySquare.compRight
#print axioms SerrePositivity.KST.ProExcision.ChainHomotopySquare.compRight

#check @SerrePositivity.KST.ProExcision.ezHomotopy_square
#print axioms SerrePositivity.KST.ProExcision.ezHomotopy_square

#check @SerrePositivity.KST.ProExcision.normalizedEZPrefix_naturality
#print axioms SerrePositivity.KST.ProExcision.normalizedEZPrefix_naturality

#check @SerrePositivity.KST.ProExcision.normalizedEZSuffix_naturality
#print axioms SerrePositivity.KST.ProExcision.normalizedEZSuffix_naturality

#check @SerrePositivity.KST.ProExcision.normalizedEZRawHomotopy_square
#print axioms SerrePositivity.KST.ProExcision.normalizedEZRawHomotopy_square

#check @SerrePositivity.KST.ProExcision.normalizedEZInsertMooreHomotopy_square
#print axioms SerrePositivity.KST.ProExcision.normalizedEZInsertMooreHomotopy_square

#check @SerrePositivity.KST.ProExcision.normalizedEZHomotopy_square
#print axioms SerrePositivity.KST.ProExcision.normalizedEZHomotopy_square

#check @SerrePositivity.KST.ProExcision.integerIntervalX
#print axioms SerrePositivity.KST.ProExcision.integerIntervalX

#check @SerrePositivity.KST.ProExcision.integerIntervalVertex
#print axioms SerrePositivity.KST.ProExcision.integerIntervalVertex

#check @SerrePositivity.KST.ProExcision.integerIntervalEdge
#print axioms SerrePositivity.KST.ProExcision.integerIntervalEdge

#check @SerrePositivity.KST.ProExcision.integerIntervalBoundary
#print axioms SerrePositivity.KST.ProExcision.integerIntervalBoundary

#check @SerrePositivity.KST.ProExcision.integerIntervalBoundary_edge
#print axioms SerrePositivity.KST.ProExcision.integerIntervalBoundary_edge

#check @SerrePositivity.KST.ProExcision.integerIntervalD
#print axioms SerrePositivity.KST.ProExcision.integerIntervalD

#check @SerrePositivity.KST.ProExcision.integerChainInterval
#print axioms SerrePositivity.KST.ProExcision.integerChainInterval

#check @SerrePositivity.KST.ProExcision.integerIntervalWeight
#print axioms SerrePositivity.KST.ProExcision.integerIntervalWeight

#check @SerrePositivity.KST.ProExcision.integerIntervalWeight_vertices
#print axioms SerrePositivity.KST.ProExcision.integerIntervalWeight_vertices

#check @SerrePositivity.KST.ProExcision.integerIntervalWeight_triangle
#print axioms SerrePositivity.KST.ProExcision.integerIntervalWeight_triangle

#check @SerrePositivity.KST.ProExcision.normalizedMapReconstruct
#print axioms SerrePositivity.KST.ProExcision.normalizedMapReconstruct

#check @SerrePositivity.KST.ProExcision.normalizedMapReconstruct_map
#print axioms SerrePositivity.KST.ProExcision.normalizedMapReconstruct_map

#check @SerrePositivity.KST.ProExcision.normalizedMap_eq_of_map_eq
#print axioms SerrePositivity.KST.ProExcision.normalizedMap_eq_of_map_eq

#check @SerrePositivity.KST.ProExcision.normalizedMapReconstruct_of_map
#print axioms SerrePositivity.KST.ProExcision.normalizedMapReconstruct_of_map

#check @SerrePositivity.KST.ProExcision.normalizedMapReconstruct_comp
#print axioms SerrePositivity.KST.ProExcision.normalizedMapReconstruct_comp

#check @SerrePositivity.KST.ProExcision.intervalSimplexVertex
#print axioms SerrePositivity.KST.ProExcision.intervalSimplexVertex

#check @SerrePositivity.KST.ProExcision.intervalSimplexVertex_map
#print axioms SerrePositivity.KST.ProExcision.intervalSimplexVertex_map

#check @SerrePositivity.KST.ProExcision.integerIntervalComparisonApp
#print axioms SerrePositivity.KST.ProExcision.integerIntervalComparisonApp

#check @SerrePositivity.KST.ProExcision.integerIntervalComparisonApp_zero_generator
#print axioms SerrePositivity.KST.ProExcision.integerIntervalComparisonApp_zero_generator

#check @SerrePositivity.KST.ProExcision.integerIntervalComparisonApp_one_generator
#print axioms SerrePositivity.KST.ProExcision.integerIntervalComparisonApp_one_generator

#check @SerrePositivity.KST.ProExcision.integerIntervalComparison_comm_zero
#print axioms SerrePositivity.KST.ProExcision.integerIntervalComparison_comm_zero

#check @SerrePositivity.KST.ProExcision.integerIntervalComparison_comm_one
#print axioms SerrePositivity.KST.ProExcision.integerIntervalComparison_comm_one

#check @SerrePositivity.KST.ProExcision.integerIntervalComparison
#print axioms SerrePositivity.KST.ProExcision.integerIntervalComparison

#check @SerrePositivity.KST.ProExcision.integerTensorFreeDesc
#print axioms SerrePositivity.KST.ProExcision.integerTensorFreeDesc

#check @SerrePositivity.KST.ProExcision.integerTensorFreeDesc_generator
#print axioms SerrePositivity.KST.ProExcision.integerTensorFreeDesc_generator

#check @SerrePositivity.KST.ProExcision.integerTensor_free_hom_ext
#print axioms SerrePositivity.KST.ProExcision.integerTensor_free_hom_ext

#check @SerrePositivity.KST.ProExcision.chainIntervalEndpointEval
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEndpointEval

#check @SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_zero
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_zero

#check @SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_one
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_one

#check @SerrePositivity.KST.ProExcision.chainIntervalEdgeEval
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEdgeEval

#check @SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_edge
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_edge

#check @SerrePositivity.KST.ProExcision.chainHomotopyIntervalBidegree
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyIntervalBidegree

#check @SerrePositivity.KST.ProExcision.chainHomotopyIntervalApp
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyIntervalApp

#check @SerrePositivity.KST.ProExcision.ι_chainHomotopyIntervalApp
#print axioms SerrePositivity.KST.ProExcision.ι_chainHomotopyIntervalApp

#check @SerrePositivity.KST.ProExcision.integerTensor_punit_hom_zero
#print axioms SerrePositivity.KST.ProExcision.integerTensor_punit_hom_zero

#check @SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_naturality
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_naturality

#check @SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_naturality
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_naturality

#check @SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_comm
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_comm

#check @SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_boundary
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEndpointEval_boundary

#check @SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_zero
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_zero

#check @SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_add
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_add

#check @SerrePositivity.KST.ProExcision.chainIntervalEdgeEvalAddHom
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEdgeEvalAddHom

#check @SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_zsmul
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_zsmul

#check @SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_comp
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_comp

#check @SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_precomp
#print axioms SerrePositivity.KST.ProExcision.chainIntervalEdgeEval_precomp

#check @SerrePositivity.KST.ProExcision.chainIntervalHomotopySign_zero
#print axioms SerrePositivity.KST.ProExcision.chainIntervalHomotopySign_zero

#check @SerrePositivity.KST.ProExcision.chainIntervalHomotopySign_succ
#print axioms SerrePositivity.KST.ProExcision.chainIntervalHomotopySign_succ

#check @SerrePositivity.KST.ProExcision.chainInterval_ι_D₁_succ
#print axioms SerrePositivity.KST.ProExcision.chainInterval_ι_D₁_succ

#check @SerrePositivity.KST.ProExcision.chainInterval_ι_D₁_zero
#print axioms SerrePositivity.KST.ProExcision.chainInterval_ι_D₁_zero

#check @SerrePositivity.KST.ProExcision.chainInterval_ι_D₂_succ
#print axioms SerrePositivity.KST.ProExcision.chainInterval_ι_D₂_succ

#check @SerrePositivity.KST.ProExcision.chainInterval_ι_D₂_zero
#print axioms SerrePositivity.KST.ProExcision.chainInterval_ι_D₂_zero

#check @SerrePositivity.KST.ProExcision.chainHomotopyInterval_comm_vertex
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyInterval_comm_vertex

#check @SerrePositivity.KST.ProExcision.chainHomotopyInterval_comm_edge_zero
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyInterval_comm_edge_zero

#check @SerrePositivity.KST.ProExcision.chainHomotopyInterval_comm_edge_succ
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyInterval_comm_edge_succ

#check @SerrePositivity.KST.ProExcision.chainHomotopyInterval_comm
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyInterval_comm

#check @SerrePositivity.KST.ProExcision.chainHomotopyInterval
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyInterval

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderMap
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderMap

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct_map
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct_map

#check @SerrePositivity.KST.ProExcision.intervalSimplexVertex_constant
#print axioms SerrePositivity.KST.ProExcision.intervalSimplexVertex_constant

#check @SerrePositivity.KST.ProExcision.intervalConstant_map
#print axioms SerrePositivity.KST.ProExcision.intervalConstant_map

#check @SerrePositivity.KST.ProExcision.integerIntervalComparison_constant_zero
#print axioms SerrePositivity.KST.ProExcision.integerIntervalComparison_constant_zero

#check @SerrePositivity.KST.ProExcision.integerIntervalComparison_constant_succ
#print axioms SerrePositivity.KST.ProExcision.integerIntervalComparison_constant_succ

#check @SerrePositivity.KST.ProExcision.integerIntervalComparison_constant_of_pos
#print axioms SerrePositivity.KST.ProExcision.integerIntervalComparison_constant_of_pos

#check @SerrePositivity.KST.ProExcision.cylinderAWTerm
#print axioms SerrePositivity.KST.ProExcision.cylinderAWTerm

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_eq_sum
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_eq_sum

#check @SerrePositivity.KST.ProExcision.cylinderAWTerm_eq
#print axioms SerrePositivity.KST.ProExcision.cylinderAWTerm_eq

#check @SerrePositivity.KST.ProExcision.cylinderAWTerm_constant_of_lt
#print axioms SerrePositivity.KST.ProExcision.cylinderAWTerm_constant_of_lt

#check @SerrePositivity.KST.ProExcision.chainHomotopyInterval_naturality
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyInterval_naturality

#check @SerrePositivity.KST.ProExcision.awFront_last
#print axioms SerrePositivity.KST.ProExcision.awFront_last

#check @SerrePositivity.KST.ProExcision.cylinderAWTerm_constant_last
#print axioms SerrePositivity.KST.ProExcision.cylinderAWTerm_constant_last

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_constant
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_constant

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_endpoint₀
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_endpoint₀

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_endpoint₁
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_endpoint₁

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderMap_endpoint₀
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderMap_endpoint₀

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderMap_endpoint₁
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderMap_endpoint₁

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct_endpoint₀
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct_endpoint₀

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct_endpoint₁
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct_endpoint₁

#check @SerrePositivity.KST.ProExcision.LinearizedHomotopy.ofNormalizedChainHomotopy
#print axioms SerrePositivity.KST.ProExcision.LinearizedHomotopy.ofNormalizedChainHomotopy

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_naturality
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderCore_naturality

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderMap_naturality
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderMap_naturality

#check @SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct_naturality
#print axioms SerrePositivity.KST.ProExcision.chainHomotopyCylinderReconstruct_naturality

#check @SerrePositivity.KST.ProExcision.normalizedMap_component_eq_projection
#print axioms SerrePositivity.KST.ProExcision.normalizedMap_component_eq_projection

#check @SerrePositivity.KST.ProExcision.simplicialMap_eq_complement_of_prev
#print axioms SerrePositivity.KST.ProExcision.simplicialMap_eq_complement_of_prev

#check @SerrePositivity.KST.ProExcision.normalizedMap_eq_low_reflect
#print axioms SerrePositivity.KST.ProExcision.normalizedMap_eq_low_reflect

#check @SerrePositivity.KST.ProExcision.chainComparisonDifferenceHomotopy
#print axioms SerrePositivity.KST.ProExcision.chainComparisonDifferenceHomotopy

#check @SerrePositivity.KST.ProExcision.normalizedComparisonCorrectedMap_eq_low
#print axioms SerrePositivity.KST.ProExcision.normalizedComparisonCorrectedMap_eq_low

#check @SerrePositivity.KST.ProExcision.linearizedMHomotopyOfChainComparisons
#print axioms SerrePositivity.KST.ProExcision.linearizedMHomotopyOfChainComparisons

#check @SerrePositivity.KST.ProExcision.normalizedMooreComplex_additive
#print axioms SerrePositivity.KST.ProExcision.normalizedMooreComplex_additive

#check @SerrePositivity.KST.ProExcision.normalizedTensorComparisonHomotopy
#print axioms SerrePositivity.KST.ProExcision.normalizedTensorComparisonHomotopy

#check @SerrePositivity.KST.ProExcision.normalizedTensorComparisonWithHomotopies
#print axioms SerrePositivity.KST.ProExcision.normalizedTensorComparisonWithHomotopies

#check @SerrePositivity.KST.ProExcision.normalizedTensorAugmentationComparison
#print axioms SerrePositivity.KST.ProExcision.normalizedTensorAugmentationComparison

#check @SerrePositivity.KST.ProExcision.linearizedTensorAugmentationMHomotopy
#print axioms SerrePositivity.KST.ProExcision.linearizedTensorAugmentationMHomotopy

#check @SerrePositivity.KST.ProExcision.nervePairMap
#print axioms SerrePositivity.KST.ProExcision.nervePairMap

#check @SerrePositivity.KST.ProExcision.groupProductFunctor
#print axioms SerrePositivity.KST.ProExcision.groupProductFunctor

#check @SerrePositivity.KST.ProExcision.groupProductNerve
#print axioms SerrePositivity.KST.ProExcision.groupProductNerve

#check @SerrePositivity.KST.ProExcision.simplicialDiagonal
#print axioms SerrePositivity.KST.ProExcision.simplicialDiagonal

#check @SerrePositivity.KST.ProExcision.groupProductNerve_comp
#print axioms SerrePositivity.KST.ProExcision.groupProductNerve_comp

#check @SerrePositivity.KST.ProExcision.linearizedDiagonal
#print axioms SerrePositivity.KST.ProExcision.linearizedDiagonal

#check @SerrePositivity.KST.ProExcision.linearizedGroupProduct
#print axioms SerrePositivity.KST.ProExcision.linearizedGroupProduct

#check @SerrePositivity.KST.ProExcision.linearizedGroupProduct_comp
#print axioms SerrePositivity.KST.ProExcision.linearizedGroupProduct_comp

#check @SerrePositivity.KST.ProExcision.groupProduct_trivial
#print axioms SerrePositivity.KST.ProExcision.groupProduct_trivial

#check @SerrePositivity.KST.ProExcision.ChainHomotopySquare.refl
#print axioms SerrePositivity.KST.ProExcision.ChainHomotopySquare.refl

#check @SerrePositivity.KST.ProExcision.ChainHomotopySquare.add
#print axioms SerrePositivity.KST.ProExcision.ChainHomotopySquare.add

#check @SerrePositivity.KST.ProExcision.ChainHomotopySquare.smul
#print axioms SerrePositivity.KST.ProExcision.ChainHomotopySquare.smul

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorHomotopy_naturality

#check @SerrePositivity.KST.ProExcision.linearizedCylinderHomotopy_generator
#print axioms SerrePositivity.KST.ProExcision.linearizedCylinderHomotopy_generator

#check @SerrePositivity.KST.ProExcision.linearizedCylinderHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedCylinderHomotopy_naturality

#check @SerrePositivity.KST.ProExcision.linearizedEndpointSimplicialHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpointSimplicialHomotopy_naturality

#check @SerrePositivity.KST.ProExcision.linearizedEndpointChainHomotopy_square
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpointChainHomotopy_square

#check @SerrePositivity.KST.ProExcision.normalizedLinearizedEndpointHomotopy_square
#print axioms SerrePositivity.KST.ProExcision.normalizedLinearizedEndpointHomotopy_square

#check @SerrePositivity.KST.ProExcision.normalizedStrictificationHomotopy_square
#print axioms SerrePositivity.KST.ProExcision.normalizedStrictificationHomotopy_square

#check @SerrePositivity.KST.ProExcision.chainComparisonDifferenceHomotopy_square
#print axioms SerrePositivity.KST.ProExcision.chainComparisonDifferenceHomotopy_square

#check @SerrePositivity.KST.ProExcision.linearizedMHomotopyOfChainComparisons_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedMHomotopyOfChainComparisons_naturality

#check @SerrePositivity.KST.ProExcision.simplicialIntegerTensorMap_comp
#print axioms SerrePositivity.KST.ProExcision.simplicialIntegerTensorMap_comp

#check @SerrePositivity.KST.ProExcision.normalizedTensorComparisonHomotopy_square
#print axioms SerrePositivity.KST.ProExcision.normalizedTensorComparisonHomotopy_square

#check @SerrePositivity.KST.ProExcision.normalizedTensorComparisonWithHomotopies_square
#print axioms SerrePositivity.KST.ProExcision.normalizedTensorComparisonWithHomotopies_square

#check @SerrePositivity.KST.ProExcision.normalizedTensorAugmentationComparison_square
#print axioms SerrePositivity.KST.ProExcision.normalizedTensorAugmentationComparison_square

#check @SerrePositivity.KST.ProExcision.constructionA5
#print axioms SerrePositivity.KST.ProExcision.constructionA5

#check @SerrePositivity.KST.ProExcision.linearizedDiagonal_generator
#print axioms SerrePositivity.KST.ProExcision.linearizedDiagonal_generator

#check @SerrePositivity.KST.ProExcision.linearizedDiagonal_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedDiagonal_naturality

#check @SerrePositivity.KST.ProExcision.linearizedGroupProduct_generator
#print axioms SerrePositivity.KST.ProExcision.linearizedGroupProduct_generator

#check @SerrePositivity.KST.ProExcision.linearizedGroupProduct_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedGroupProduct_naturality

#check @SerrePositivity.KST.ProExcision.normalizedTensorSandwich_naturality
#print axioms SerrePositivity.KST.ProExcision.normalizedTensorSandwich_naturality

#check @SerrePositivity.KST.ProExcision.chainComparisonWhisker_naturality
#print axioms SerrePositivity.KST.ProExcision.chainComparisonWhisker_naturality

#check @SerrePositivity.KST.ProExcision.normalizedComparisonWhisker_square
#print axioms SerrePositivity.KST.ProExcision.normalizedComparisonWhisker_square

#check @SerrePositivity.KST.ProExcision.linearizedTensorAugmentationMHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedTensorAugmentationMHomotopy_naturality

#check @SerrePositivity.KST.ProExcision.discreteNerveAction_linearized
#print axioms SerrePositivity.KST.ProExcision.discreteNerveAction_linearized

#check @SerrePositivity.KST.ProExcision.LinearizedEquivariant.discrete_naturality
#print axioms SerrePositivity.KST.ProExcision.LinearizedEquivariant.discrete_naturality

#check @SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.discrete_naturality
#print axioms SerrePositivity.KST.ProExcision.LinearizedCylinderEquivariant.discrete_naturality

#check @SerrePositivity.KST.ProExcision.constructionA5_equivariant
#print axioms SerrePositivity.KST.ProExcision.constructionA5_equivariant

#check @SerrePositivity.KST.ProExcision.constructionA5EquivariantCylinderMap
#print axioms SerrePositivity.KST.ProExcision.constructionA5EquivariantCylinderMap

#check @SerrePositivity.KST.ProExcision.IsCentralElement
#print axioms SerrePositivity.KST.ProExcision.IsCentralElement

#check @SerrePositivity.KST.ProExcision.rightMultiplication
#print axioms SerrePositivity.KST.ProExcision.rightMultiplication

#check @SerrePositivity.KST.ProExcision.vectorRightMultiplication
#print axioms SerrePositivity.KST.ProExcision.vectorRightMultiplication

#check @SerrePositivity.KST.ProExcision.vectorRightMultiplication_mulVec
#print axioms SerrePositivity.KST.ProExcision.vectorRightMultiplication_mulVec

#check @SerrePositivity.KST.ProExcision.centralMultiplicationIdeal
#print axioms SerrePositivity.KST.ProExcision.centralMultiplicationIdeal

#check @SerrePositivity.KST.ProExcision.mem_centralMultiplicationIdeal
#print axioms SerrePositivity.KST.ProExcision.mem_centralMultiplicationIdeal

#check @SerrePositivity.KST.ProExcision.mem_centralMultiplicationIdeal_iff_right
#print axioms SerrePositivity.KST.ProExcision.mem_centralMultiplicationIdeal_iff_right

#check @SerrePositivity.KST.ProExcision.rightMultiplication_injective
#print axioms SerrePositivity.KST.ProExcision.rightMultiplication_injective

#check @SerrePositivity.KST.ProExcision.rightMultiplication_naturality
#print axioms SerrePositivity.KST.ProExcision.rightMultiplication_naturality

#check @SerrePositivity.KST.ProExcision.vectorRightMultiplication_naturality
#print axioms SerrePositivity.KST.ProExcision.vectorRightMultiplication_naturality

#check @SerrePositivity.KST.ProExcision.centralMultiplicationIdeal_map_mem
#print axioms SerrePositivity.KST.ProExcision.centralMultiplicationIdeal_map_mem

#check @SerrePositivity.KST.ProExcision.squareZeroUnit
#print axioms SerrePositivity.KST.ProExcision.squareZeroUnit

#check @SerrePositivity.KST.ProExcision.squareZero_conjugation
#print axioms SerrePositivity.KST.ProExcision.squareZero_conjugation

#check @SerrePositivity.KST.ProExcision.squareZero_mul_of_reverse_zero
#print axioms SerrePositivity.KST.ProExcision.squareZero_mul_of_reverse_zero

#check @SerrePositivity.KST.ProExcision.squareZeroUnit_conjugation
#print axioms SerrePositivity.KST.ProExcision.squareZeroUnit_conjugation

#check @SerrePositivity.KST.ProExcision.blockColumn
#print axioms SerrePositivity.KST.ProExcision.blockColumn

#check @SerrePositivity.KST.ProExcision.blockColumn_square_zero
#print axioms SerrePositivity.KST.ProExcision.blockColumn_square_zero

#check @SerrePositivity.KST.ProExcision.blockColumn_mul_aux
#print axioms SerrePositivity.KST.ProExcision.blockColumn_mul_aux

#check @SerrePositivity.KST.ProExcision.aux_mul_blockColumn_zero
#print axioms SerrePositivity.KST.ProExcision.aux_mul_blockColumn_zero

#check @SerrePositivity.KST.ProExcision.blockColumn_conjugation
#print axioms SerrePositivity.KST.ProExcision.blockColumn_conjugation

#check @SerrePositivity.KST.ProExcision.matrix_mul_single_of_fixed_column
#print axioms SerrePositivity.KST.ProExcision.matrix_mul_single_of_fixed_column

#check @SerrePositivity.KST.ProExcision.matrix_single_mul_of_fixed_row
#print axioms SerrePositivity.KST.ProExcision.matrix_single_mul_of_fixed_row

#check @SerrePositivity.KST.ProExcision.matrix_commute_one_add_blockColumn
#print axioms SerrePositivity.KST.ProExcision.matrix_commute_one_add_blockColumn

#check @SerrePositivity.KST.ProExcision.blockColumn_mul_zero
#print axioms SerrePositivity.KST.ProExcision.blockColumn_mul_zero

#check @SerrePositivity.KST.ProExcision.blockColumn_add
#print axioms SerrePositivity.KST.ProExcision.blockColumn_add

#check @SerrePositivity.KST.ProExcision.blockColumnHom
#print axioms SerrePositivity.KST.ProExcision.blockColumnHom

#check @SerrePositivity.KST.ProExcision.commutingProductHom
#print axioms SerrePositivity.KST.ProExcision.commutingProductHom

#check @SerrePositivity.KST.ProExcision.groupLinearizedMap_zero_eq
#print axioms SerrePositivity.KST.ProExcision.groupLinearizedMap_zero_eq

#check @SerrePositivity.KST.ProExcision.groupZeroMHomotopy
#print axioms SerrePositivity.KST.ProExcision.groupZeroMHomotopy

#check @SerrePositivity.KST.ProExcision.groupZeroMHomotopy_equivariant
#print axioms SerrePositivity.KST.ProExcision.groupZeroMHomotopy_equivariant

#check @SerrePositivity.KST.ProExcision.matrix_mul_fixed_column
#print axioms SerrePositivity.KST.ProExcision.matrix_mul_fixed_column

#check @SerrePositivity.KST.ProExcision.matrix_mul_fixed_row
#print axioms SerrePositivity.KST.ProExcision.matrix_mul_fixed_row

#check @SerrePositivity.KST.ProExcision.fixedBlockSubgroup
#print axioms SerrePositivity.KST.ProExcision.fixedBlockSubgroup

#check @SerrePositivity.KST.ProExcision.fixedBlockSubgroup_commute_column
#print axioms SerrePositivity.KST.ProExcision.fixedBlockSubgroup_commute_column

#check @SerrePositivity.KST.ProExcision.fixedBlockProduct
#print axioms SerrePositivity.KST.ProExcision.fixedBlockProduct

#check @SerrePositivity.KST.ProExcision.blockPatternSubring
#print axioms SerrePositivity.KST.ProExcision.blockPatternSubring

#check @SerrePositivity.KST.ProExcision.oneDifference_mul_mem
#print axioms SerrePositivity.KST.ProExcision.oneDifference_mul_mem

#check @SerrePositivity.KST.ProExcision.oneDifferenceSubgroup
#print axioms SerrePositivity.KST.ProExcision.oneDifferenceSubgroup

#check @SerrePositivity.KST.ProExcision.triangularBlockGroup
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroup

#check @SerrePositivity.KST.ProExcision.triangularBlockGroup_fixed_column
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroup_fixed_column

#check @SerrePositivity.KST.ProExcision.triangularBlockGroup_fixed_max_row
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroup_fixed_max_row

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdeal
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdeal

#check @SerrePositivity.KST.ProExcision.mem_integerUnitizationIdeal
#print axioms SerrePositivity.KST.ProExcision.mem_integerUnitizationIdeal

#check @SerrePositivity.KST.ProExcision.inr_mem_integerUnitizationIdeal
#print axioms SerrePositivity.KST.ProExcision.inr_mem_integerUnitizationIdeal

#check @SerrePositivity.KST.ProExcision.mem_integerUnitizationIdeal_iff
#print axioms SerrePositivity.KST.ProExcision.mem_integerUnitizationIdeal_iff

#check @SerrePositivity.KST.ProExcision.nonUnitalTriangularBlockGroup
#print axioms SerrePositivity.KST.ProExcision.nonUnitalTriangularBlockGroup

#check @SerrePositivity.KST.ProExcision.single_mem_blockPattern
#print axioms SerrePositivity.KST.ProExcision.single_mem_blockPattern

#check @SerrePositivity.KST.ProExcision.blockColumn_mem_blockPattern
#print axioms SerrePositivity.KST.ProExcision.blockColumn_mem_blockPattern

#check @SerrePositivity.KST.ProExcision.squareZeroUnit_mem_oneDifference
#print axioms SerrePositivity.KST.ProExcision.squareZeroUnit_mem_oneDifference

#check @SerrePositivity.KST.ProExcision.blockColumnHom_mem_triangularBlockGroup
#print axioms SerrePositivity.KST.ProExcision.blockColumnHom_mem_triangularBlockGroup

#check @SerrePositivity.KST.ProExcision.oneDifferenceSubgroupMap
#print axioms SerrePositivity.KST.ProExcision.oneDifferenceSubgroupMap

#check @SerrePositivity.KST.ProExcision.map_mem_blockPattern
#print axioms SerrePositivity.KST.ProExcision.map_mem_blockPattern

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupMap
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupMap

#check @SerrePositivity.KST.ProExcision.optionMatrixExtension
#print axioms SerrePositivity.KST.ProExcision.optionMatrixExtension

#check @SerrePositivity.KST.ProExcision.optionMatrixExtensionHom
#print axioms SerrePositivity.KST.ProExcision.optionMatrixExtensionHom

#check @SerrePositivity.KST.ProExcision.matrixInsertionHom
#print axioms SerrePositivity.KST.ProExcision.matrixInsertionHom

#check @SerrePositivity.KST.ProExcision.matrixInsertionUnits
#print axioms SerrePositivity.KST.ProExcision.matrixInsertionUnits

#check @SerrePositivity.KST.ProExcision.matrixInsertion_succAbove
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_succAbove

#check @SerrePositivity.KST.ProExcision.matrixInsertion_self
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_self

#check @SerrePositivity.KST.ProExcision.matrixInsertion_row
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_row

#check @SerrePositivity.KST.ProExcision.matrixInsertion_column
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_column

#check @SerrePositivity.KST.ProExcision.matrixInsertion_difference_succAbove
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_difference_succAbove

#check @SerrePositivity.KST.ProExcision.insertion_index_le
#print axioms SerrePositivity.KST.ProExcision.insertion_index_le

#check @SerrePositivity.KST.ProExcision.matrixInsertion_difference_mem_blockPattern
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_difference_mem_blockPattern

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupInsertion
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupInsertion

#check @SerrePositivity.KST.ProExcision.matrixInsertion_fixed_row
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_fixed_row

#check @SerrePositivity.KST.ProExcision.matrixInsertion_fixed_column
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_fixed_column

#check @SerrePositivity.KST.ProExcision.triangularBlockInsertionFixedHom
#print axioms SerrePositivity.KST.ProExcision.triangularBlockInsertionFixedHom

#check @SerrePositivity.KST.ProExcision.idealVectorInclusion
#print axioms SerrePositivity.KST.ProExcision.idealVectorInclusion

#check @SerrePositivity.KST.ProExcision.idealBlockColumnHom
#print axioms SerrePositivity.KST.ProExcision.idealBlockColumnHom

#check @SerrePositivity.KST.ProExcision.insertion_first_rows_lt
#print axioms SerrePositivity.KST.ProExcision.insertion_first_rows_lt

#check @SerrePositivity.KST.ProExcision.triangularBlockInsertion_commute_column
#print axioms SerrePositivity.KST.ProExcision.triangularBlockInsertion_commute_column

#check @SerrePositivity.KST.ProExcision.triangularBlockProductHom
#print axioms SerrePositivity.KST.ProExcision.triangularBlockProductHom

#check @SerrePositivity.KST.ProExcision.idealRightMultiplication
#print axioms SerrePositivity.KST.ProExcision.idealRightMultiplication

#check @SerrePositivity.KST.ProExcision.idealVectorRightHom
#print axioms SerrePositivity.KST.ProExcision.idealVectorRightHom

#check @SerrePositivity.KST.ProExcision.firstRows_lt_last
#print axioms SerrePositivity.KST.ProExcision.firstRows_lt_last

#check @SerrePositivity.KST.ProExcision.lastBlockColumnHom
#print axioms SerrePositivity.KST.ProExcision.lastBlockColumnHom

#check @SerrePositivity.KST.ProExcision.lastRightColumnHom
#print axioms SerrePositivity.KST.ProExcision.lastRightColumnHom

#check @SerrePositivity.KST.ProExcision.groupLinearizedMap_comp
#print axioms SerrePositivity.KST.ProExcision.groupLinearizedMap_comp

#check @SerrePositivity.KST.ProExcision.groupLinearizedMap_id
#print axioms SerrePositivity.KST.ProExcision.groupLinearizedMap_id

#check @SerrePositivity.KST.ProExcision.groupConjugationMHomotopy
#print axioms SerrePositivity.KST.ProExcision.groupConjugationMHomotopy

#check @SerrePositivity.KST.ProExcision.blockColumn_succAbove
#print axioms SerrePositivity.KST.ProExcision.blockColumn_succAbove

#check @SerrePositivity.KST.ProExcision.blockColumn_succAbove_row
#print axioms SerrePositivity.KST.ProExcision.blockColumn_succAbove_row

#check @SerrePositivity.KST.ProExcision.blockColumn_succAbove_column
#print axioms SerrePositivity.KST.ProExcision.blockColumn_succAbove_column

#check @SerrePositivity.KST.ProExcision.matrixInsertion_one_add_blockColumn
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_one_add_blockColumn

#check @SerrePositivity.KST.ProExcision.auxiliaryBlockIndex
#print axioms SerrePositivity.KST.ProExcision.auxiliaryBlockIndex

#check @SerrePositivity.KST.ProExcision.auxiliaryBlockUnit
#print axioms SerrePositivity.KST.ProExcision.auxiliaryBlockUnit

#check @SerrePositivity.KST.ProExcision.auxiliaryBlockColumnHom
#print axioms SerrePositivity.KST.ProExcision.auxiliaryBlockColumnHom

#check @SerrePositivity.KST.ProExcision.auxiliaryBlockUnit_conjugation
#print axioms SerrePositivity.KST.ProExcision.auxiliaryBlockUnit_conjugation

#check @SerrePositivity.KST.ProExcision.auxiliaryInsertion_first_rows
#print axioms SerrePositivity.KST.ProExcision.auxiliaryInsertion_first_rows

#check @SerrePositivity.KST.ProExcision.auxiliaryInsertion_last
#print axioms SerrePositivity.KST.ProExcision.auxiliaryInsertion_last

#check @SerrePositivity.KST.ProExcision.triangularInsertion_lastRightColumn
#print axioms SerrePositivity.KST.ProExcision.triangularInsertion_lastRightColumn

#check @SerrePositivity.KST.ProExcision.lemma416GroupData
#print axioms SerrePositivity.KST.ProExcision.lemma416GroupData

#check @SerrePositivity.KST.ProExcision.lemma416GroupData_left
#print axioms SerrePositivity.KST.ProExcision.lemma416GroupData_left

#check @SerrePositivity.KST.ProExcision.lemma416GroupData_right
#print axioms SerrePositivity.KST.ProExcision.lemma416GroupData_right

#check @SerrePositivity.KST.ProExcision.lemma416GroupData_product
#print axioms SerrePositivity.KST.ProExcision.lemma416GroupData_product

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.congr
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.congr

#check @SerrePositivity.KST.ProExcision.lemma416HomotopyStep
#print axioms SerrePositivity.KST.ProExcision.lemma416HomotopyStep

#check @SerrePositivity.KST.ProExcision.lemma416Homotopy
#print axioms SerrePositivity.KST.ProExcision.lemma416Homotopy

#check @SerrePositivity.KST.ProExcision.oneDifferenceElement
#print axioms SerrePositivity.KST.ProExcision.oneDifferenceElement

#check @SerrePositivity.KST.ProExcision.oneDifferenceElement_mul
#print axioms SerrePositivity.KST.ProExcision.oneDifferenceElement_mul

#check @SerrePositivity.KST.ProExcision.oneDifferenceElement_inv_relation
#print axioms SerrePositivity.KST.ProExcision.oneDifferenceElement_inv_relation

#check @SerrePositivity.KST.ProExcision.oneDifferenceTransform
#print axioms SerrePositivity.KST.ProExcision.oneDifferenceTransform

#check @SerrePositivity.KST.ProExcision.leftMultiplierHom
#print axioms SerrePositivity.KST.ProExcision.leftMultiplierHom

#check @SerrePositivity.KST.ProExcision.leftMultiplierGroupHom
#print axioms SerrePositivity.KST.ProExcision.leftMultiplierGroupHom

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_left_left
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_left_left

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_left_right
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_left_right

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_right_left
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_right_left

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_right_right
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_right_right

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_mul_firstRows
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_mul_firstRows

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_mul_otherRows
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_mul_otherRows

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_right_absorbed
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_right_absorbed

#check @SerrePositivity.KST.ProExcision.blockPattern_firstBlock_right_absorbed
#print axioms SerrePositivity.KST.ProExcision.blockPattern_firstBlock_right_absorbed

#check @SerrePositivity.KST.ProExcision.blockPattern_firstBlock_left_mem
#print axioms SerrePositivity.KST.ProExcision.blockPattern_firstBlock_left_mem

#check @SerrePositivity.KST.ProExcision.triangularBlockMatrixEnd
#print axioms SerrePositivity.KST.ProExcision.triangularBlockMatrixEnd

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_one
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_one

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_mul
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_mul

#check @SerrePositivity.KST.ProExcision.triangularBlockMatrixEnd_val
#print axioms SerrePositivity.KST.ProExcision.triangularBlockMatrixEnd_val

#check @SerrePositivity.KST.ProExcision.triangularBlockMatrixAction
#print axioms SerrePositivity.KST.ProExcision.triangularBlockMatrixAction

#check @SerrePositivity.KST.ProExcision.idealMatrixVecHom
#print axioms SerrePositivity.KST.ProExcision.idealMatrixVecHom

#check @SerrePositivity.KST.ProExcision.idealMatrixAction
#print axioms SerrePositivity.KST.ProExcision.idealMatrixAction

#check @SerrePositivity.KST.ProExcision.idealVectorRightHom_equivariant
#print axioms SerrePositivity.KST.ProExcision.idealVectorRightHom_equivariant

#check @SerrePositivity.KST.ProExcision.firstRows_blockColumn_apply
#print axioms SerrePositivity.KST.ProExcision.firstRows_blockColumn_apply

#check @SerrePositivity.KST.ProExcision.otherRows_blockColumn_apply
#print axioms SerrePositivity.KST.ProExcision.otherRows_blockColumn_apply

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_mul_blockColumn
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_mul_blockColumn

#check @SerrePositivity.KST.ProExcision.idealBlockColumnHom_equivariant
#print axioms SerrePositivity.KST.ProExcision.idealBlockColumnHom_equivariant

#check @SerrePositivity.KST.ProExcision.lastBlockColumnHom_equivariant
#print axioms SerrePositivity.KST.ProExcision.lastBlockColumnHom_equivariant

#check @SerrePositivity.KST.ProExcision.lastRightColumnHom_equivariant
#print axioms SerrePositivity.KST.ProExcision.lastRightColumnHom_equivariant

#check @SerrePositivity.KST.ProExcision.auxiliaryBlockColumnHom_equivariant
#print axioms SerrePositivity.KST.ProExcision.auxiliaryBlockColumnHom_equivariant

#check @SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_firstRows
#print axioms SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_firstRows

#check @SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_otherRows
#print axioms SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_otherRows

#check @SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_preserves_fixed_column
#print axioms SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_preserves_fixed_column

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_fixed_aux_column
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_fixed_aux_column

#check @SerrePositivity.KST.ProExcision.auxiliaryBlockUnit_fixed
#print axioms SerrePositivity.KST.ProExcision.auxiliaryBlockUnit_fixed

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.precomp_equivariant
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.precomp_equivariant

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.trans_equivariant
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.trans_equivariant

#check @SerrePositivity.KST.ProExcision.groupConjugationMHomotopy_equivariant
#print axioms SerrePositivity.KST.ProExcision.groupConjugationMHomotopy_equivariant

#check @SerrePositivity.KST.ProExcision.affineMatrixAction
#print axioms SerrePositivity.KST.ProExcision.affineMatrixAction

#check @SerrePositivity.KST.ProExcision.affineMatrixAction_firstRows
#print axioms SerrePositivity.KST.ProExcision.affineMatrixAction_firstRows

#check @SerrePositivity.KST.ProExcision.affineMatrixAction_otherRows
#print axioms SerrePositivity.KST.ProExcision.affineMatrixAction_otherRows

#check @SerrePositivity.KST.ProExcision.affineMatrixAction_fixed_column
#print axioms SerrePositivity.KST.ProExcision.affineMatrixAction_fixed_column

#check @SerrePositivity.KST.ProExcision.insertion_preserves_firstRows
#print axioms SerrePositivity.KST.ProExcision.insertion_preserves_firstRows

#check @SerrePositivity.KST.ProExcision.matrixInsertion_fixed_new_column
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_fixed_new_column

#check @SerrePositivity.KST.ProExcision.affineMatrixAction_insertion
#print axioms SerrePositivity.KST.ProExcision.affineMatrixAction_insertion

#check @SerrePositivity.KST.ProExcision.triangularBlockInsertion_equivariant
#print axioms SerrePositivity.KST.ProExcision.triangularBlockInsertion_equivariant

#check @SerrePositivity.KST.ProExcision.lemma416GroupData_mu_apply
#print axioms SerrePositivity.KST.ProExcision.lemma416GroupData_mu_apply

#check @SerrePositivity.KST.ProExcision.lemma416GroupData_mu_equivariant
#print axioms SerrePositivity.KST.ProExcision.lemma416GroupData_mu_equivariant

#check @SerrePositivity.KST.ProExcision.lemma416EquivariantGroupData
#print axioms SerrePositivity.KST.ProExcision.lemma416EquivariantGroupData

#check @SerrePositivity.KST.ProExcision.lemma416HomotopyStep_equivariant
#print axioms SerrePositivity.KST.ProExcision.lemma416HomotopyStep_equivariant

#check @SerrePositivity.KST.ProExcision.lemma416Homotopy_equivariant
#print axioms SerrePositivity.KST.ProExcision.lemma416Homotopy_equivariant

#check @SerrePositivity.KST.ProExcision.linearizedCylinderProjection_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedCylinderProjection_naturality

#check @SerrePositivity.KST.ProExcision.strictificationEndpoint₀_naturality
#print axioms SerrePositivity.KST.ProExcision.strictificationEndpoint₀_naturality

#check @SerrePositivity.KST.ProExcision.strictificationEndpoint₁_naturality
#print axioms SerrePositivity.KST.ProExcision.strictificationEndpoint₁_naturality

#check @SerrePositivity.KST.ProExcision.strictifiedMap_naturality
#print axioms SerrePositivity.KST.ProExcision.strictifiedMap_naturality

#check @SerrePositivity.KST.ProExcision.strictificationHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.strictificationHomotopy_naturality

#check @SerrePositivity.KST.ProExcision.chainComparisonWhisker_square
#print axioms SerrePositivity.KST.ProExcision.chainComparisonWhisker_square

#check @SerrePositivity.KST.ProExcision.linearizedTensorAugmentationMHomotopy_functorial
#print axioms SerrePositivity.KST.ProExcision.linearizedTensorAugmentationMHomotopy_functorial

#check @SerrePositivity.KST.ProExcision.groupLinearizedMap_square
#print axioms SerrePositivity.KST.ProExcision.groupLinearizedMap_square

#check @SerrePositivity.KST.ProExcision.constructionA5_functorial
#print axioms SerrePositivity.KST.ProExcision.constructionA5_functorial

#check @SerrePositivity.KST.ProExcision.idealCoefficientAddHom
#print axioms SerrePositivity.KST.ProExcision.idealCoefficientAddHom

#check @SerrePositivity.KST.ProExcision.idealVectorMap
#print axioms SerrePositivity.KST.ProExcision.idealVectorMap

#check @SerrePositivity.KST.ProExcision.idealVectorRightHom_functorial
#print axioms SerrePositivity.KST.ProExcision.idealVectorRightHom_functorial

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupMap_val
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupMap_val

#check @SerrePositivity.KST.ProExcision.blockColumn_coefficient_map
#print axioms SerrePositivity.KST.ProExcision.blockColumn_coefficient_map

#check @SerrePositivity.KST.ProExcision.idealBlockColumnHom_functorial
#print axioms SerrePositivity.KST.ProExcision.idealBlockColumnHom_functorial

#check @SerrePositivity.KST.ProExcision.lastRightColumnHom_functorial
#print axioms SerrePositivity.KST.ProExcision.lastRightColumnHom_functorial

#check @SerrePositivity.KST.ProExcision.auxiliaryBlockColumnHom_functorial
#print axioms SerrePositivity.KST.ProExcision.auxiliaryBlockColumnHom_functorial

#check @SerrePositivity.KST.ProExcision.matrixInsertion_coefficient_map
#print axioms SerrePositivity.KST.ProExcision.matrixInsertion_coefficient_map

#check @SerrePositivity.KST.ProExcision.triangularBlockInsertion_functorial
#print axioms SerrePositivity.KST.ProExcision.triangularBlockInsertion_functorial

#check @SerrePositivity.KST.ProExcision.auxiliaryBlockUnit_functorial
#print axioms SerrePositivity.KST.ProExcision.auxiliaryBlockUnit_functorial

#check @SerrePositivity.KST.ProExcision.simplicialIntegerTensorInterval_square
#print axioms SerrePositivity.KST.ProExcision.simplicialIntegerTensorInterval_square

#check @SerrePositivity.KST.ProExcision.groupZeroMHomotopy_functorial
#print axioms SerrePositivity.KST.ProExcision.groupZeroMHomotopy_functorial

#check @SerrePositivity.KST.ProExcision.groupConjugationMHomotopy_functorial
#print axioms SerrePositivity.KST.ProExcision.groupConjugationMHomotopy_functorial

#check @SerrePositivity.KST.ProExcision.lemma416GroupData_mu_functorial
#print axioms SerrePositivity.KST.ProExcision.lemma416GroupData_mu_functorial

#check @SerrePositivity.KST.ProExcision.lemma416GroupData_product_functorial
#print axioms SerrePositivity.KST.ProExcision.lemma416GroupData_product_functorial

#check @SerrePositivity.KST.ProExcision.cylinderSquare_add
#print axioms SerrePositivity.KST.ProExcision.cylinderSquare_add

#check @SerrePositivity.KST.ProExcision.cylinderSquare_sub
#print axioms SerrePositivity.KST.ProExcision.cylinderSquare_sub

#check @SerrePositivity.KST.ProExcision.cylinderSquare_constant
#print axioms SerrePositivity.KST.ProExcision.cylinderSquare_constant

#check @SerrePositivity.KST.ProExcision.lemma416HomotopyStep_functorial
#print axioms SerrePositivity.KST.ProExcision.lemma416HomotopyStep_functorial

#check @SerrePositivity.KST.ProExcision.lemma416Homotopy_functorial
#print axioms SerrePositivity.KST.ProExcision.lemma416Homotopy_functorial

#check @SerrePositivity.KST.ProExcision.simplicialGroupBar
#print axioms SerrePositivity.KST.ProExcision.simplicialGroupBar

#check @SerrePositivity.KST.ProExcision.simplicialGroupBarMap
#print axioms SerrePositivity.KST.ProExcision.simplicialGroupBarMap

#check @SerrePositivity.KST.ProExcision.linearizedGroupBar_map_decomposition
#print axioms SerrePositivity.KST.ProExcision.linearizedGroupBar_map_decomposition

#check @SerrePositivity.KST.ProExcision.linearizedGroupBar_cylinder_decomposition
#print axioms SerrePositivity.KST.ProExcision.linearizedGroupBar_cylinder_decomposition

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData

#check @SerrePositivity.KST.ProExcision.simplexVertexMap
#print axioms SerrePositivity.KST.ProExcision.simplexVertexMap

#check @SerrePositivity.KST.ProExcision.simplexVertexMap_comp
#print axioms SerrePositivity.KST.ProExcision.simplexVertexMap_comp

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.vertexElement
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.vertexElement

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.vertexElement_natural
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.vertexElement_natural

#check @SerrePositivity.KST.ProExcision.diagonalGroupCylinderMap
#print axioms SerrePositivity.KST.ProExcision.diagonalGroupCylinderMap

#check @SerrePositivity.KST.ProExcision.diagonalGroupMHomotopy
#print axioms SerrePositivity.KST.ProExcision.diagonalGroupMHomotopy

#check @SerrePositivity.KST.ProExcision.idealVectorMap_id
#print axioms SerrePositivity.KST.ProExcision.idealVectorMap_id

#check @SerrePositivity.KST.ProExcision.idealVectorMap_comp
#print axioms SerrePositivity.KST.ProExcision.idealVectorMap_comp

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupMap_id
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupMap_id

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupMap_comp
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupMap_comp

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.columnGroup
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.columnGroup

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.triangularGroup
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.triangularGroup

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.rightColumnMap
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.rightColumnMap

#check @SerrePositivity.KST.ProExcision.simplicialGroupTrivialMap
#print axioms SerrePositivity.KST.ProExcision.simplicialGroupTrivialMap

#check @SerrePositivity.KST.ProExcision.simplicialLemma416Homotopy
#print axioms SerrePositivity.KST.ProExcision.simplicialLemma416Homotopy

#check @SerrePositivity.KST.ProExcision.idealMatrixAction_functorial
#print axioms SerrePositivity.KST.ProExcision.idealMatrixAction_functorial

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_coefficient_map
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_coefficient_map

#check @SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_functorial
#print axioms SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_functorial

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.matrixMonoid
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.matrixMonoid

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.columnMatrixAction
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.columnMatrixAction

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.triangularMatrixAction
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.triangularMatrixAction

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.rightColumnActionHom
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.rightColumnActionHom

#check @SerrePositivity.KST.ProExcision.simplicialLemma416Homotopy_equivariant
#print axioms SerrePositivity.KST.ProExcision.simplicialLemma416Homotopy_equivariant

#check @SerrePositivity.KST.ProExcision.lemma416
#print axioms SerrePositivity.KST.ProExcision.lemma416

#check @SerrePositivity.KST.ProExcision.SimplicialMonoidAction.restrict
#print axioms SerrePositivity.KST.ProExcision.SimplicialMonoidAction.restrict

#check @SerrePositivity.KST.ProExcision.SimplicialActionHom.restrict
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionHom.restrict

#check @SerrePositivity.KST.ProExcision.HomologicallyMConstant.restrict
#print axioms SerrePositivity.KST.ProExcision.HomologicallyMConstant.restrict

#check @SerrePositivity.KST.ProExcision.lemma416_restrict
#print axioms SerrePositivity.KST.ProExcision.lemma416_restrict

#check @SerrePositivity.KST.ProExcision.lemma416_relative_zero
#print axioms SerrePositivity.KST.ProExcision.lemma416_relative_zero

#check @SerrePositivity.KST.ProExcision.integerNonUnitalAlgHom
#print axioms SerrePositivity.KST.ProExcision.integerNonUnitalAlgHom

#check @SerrePositivity.KST.ProExcision.integerUnitizationMap
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMap

#check @SerrePositivity.KST.ProExcision.integerUnitizationMap_fst
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMap_fst

#check @SerrePositivity.KST.ProExcision.integerUnitizationMap_snd
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMap_snd

#check @SerrePositivity.KST.ProExcision.integerUnitizationMap_inr
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMap_inr

#check @SerrePositivity.KST.ProExcision.integerUnitizationMap_id
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMap_id

#check @SerrePositivity.KST.ProExcision.integerUnitizationMap_comp
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMap_comp

#check @SerrePositivity.KST.ProExcision.integerUnitizationMap_ideal
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMap_ideal

#check @SerrePositivity.KST.ProExcision.NonUnitalRingObject
#print axioms SerrePositivity.KST.ProExcision.NonUnitalRingObject

#check @SerrePositivity.KST.ProExcision.nonUnitalRingObjectCoeSort
#print axioms SerrePositivity.KST.ProExcision.nonUnitalRingObjectCoeSort

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.standardIdeal
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.standardIdeal

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.standardElement
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.standardElement

#check @SerrePositivity.KST.ProExcision.nonUnitalLemma416
#print axioms SerrePositivity.KST.ProExcision.nonUnitalLemma416

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealAddEquiv
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealAddEquiv

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealAddEquiv_natural
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealAddEquiv_natural

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealVectorAddEquiv
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealVectorAddEquiv

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLSubmonoid
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLSubmonoid

#check @SerrePositivity.KST.ProExcision.integerUnitizationMap_fst_matrix
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMap_fst_matrix

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLPullback
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLPullback

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGL
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGL

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLRepresentation
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLRepresentation

#check @SerrePositivity.KST.ProExcision.triangularBlockGroup_fst
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroup_fst

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularHatGLHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularHatGLHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularHatGLMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularHatGLMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularHatGLHom_injective
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularHatGLHom_injective

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.fst_edge
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.fst_edge

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.componentsFst
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.componentsFst

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.componentsFst_matrix
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.componentsFst_matrix

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLAmbientMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLAmbientMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLEdgeOfCoefficients
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLEdgeOfCoefficients

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLClassMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLClassMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLClassMap_mk
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLClassMap_mk

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLClassMap_injective
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLClassMap_injective

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGL_inverse_vertex
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGL_inverse_vertex

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGL_isGrouplike
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGL_isGrouplike

#check @SerrePositivity.KST.ProExcision.nonUnitalLemma416_relative_zero
#print axioms SerrePositivity.KST.ProExcision.nonUnitalLemma416_relative_zero

#check @SerrePositivity.KST.ProExcision.matrixDropLast
#print axioms SerrePositivity.KST.ProExcision.matrixDropLast

#check @SerrePositivity.KST.ProExcision.matrixLastColumn
#print axioms SerrePositivity.KST.ProExcision.matrixLastColumn

#check @SerrePositivity.KST.ProExcision.matrixDropLast_one
#print axioms SerrePositivity.KST.ProExcision.matrixDropLast_one

#check @SerrePositivity.KST.ProExcision.matrixLastColumn_one
#print axioms SerrePositivity.KST.ProExcision.matrixLastColumn_one

#check @SerrePositivity.KST.ProExcision.matrixDropLast_mul
#print axioms SerrePositivity.KST.ProExcision.matrixDropLast_mul

#check @SerrePositivity.KST.ProExcision.matrixLastColumn_mul
#print axioms SerrePositivity.KST.ProExcision.matrixLastColumn_mul

#check @SerrePositivity.KST.ProExcision.triangularBlockGroup_lastRow
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroup_lastRow

#check @SerrePositivity.KST.ProExcision.triangularBlockGroup_dropLast_mem
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroup_dropLast_mem

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupDropLastUnit
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupDropLastUnit

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupDropLast
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupDropLast

#check @SerrePositivity.KST.ProExcision.triangularBlockGroup_lastColumn_mem
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroup_lastColumn_mem

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupLastColumn
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupLastColumn

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupLastColumn_one
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupLastColumn_one

#check @SerrePositivity.KST.ProExcision.triangularBlockGroupLastColumn_mul
#print axioms SerrePositivity.KST.ProExcision.triangularBlockGroupLastColumn_mul

#check @SerrePositivity.KST.ProExcision.triangularColumnAction
#print axioms SerrePositivity.KST.ProExcision.triangularColumnAction

#check @SerrePositivity.KST.ProExcision.triangularColumnActionStructure
#print axioms SerrePositivity.KST.ProExcision.triangularColumnActionStructure

#check @SerrePositivity.KST.ProExcision.triangularBlockAffineSplit
#print axioms SerrePositivity.KST.ProExcision.triangularBlockAffineSplit

#check @SerrePositivity.KST.ProExcision.actionProductLift
#print axioms SerrePositivity.KST.ProExcision.actionProductLift

#check @SerrePositivity.KST.ProExcision.actionProductLift_section
#print axioms SerrePositivity.KST.ProExcision.actionProductLift_section

#check @SerrePositivity.KST.ProExcision.actionProductLift_fiber
#print axioms SerrePositivity.KST.ProExcision.actionProductLift_fiber

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.triangularColumnAction
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.triangularColumnAction

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.triangularAffineSplitMap
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.triangularAffineSplitMap

#check @SerrePositivity.KST.ProExcision.firstBlockMatrixHom
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrixHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLBlockHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLBlockHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLBlockMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLBlockMap

#check @SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_intertwining
#print axioms SerrePositivity.KST.ProExcision.triangularBlockMatrixAction_intertwining

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularGLAction
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularGLAction

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularGLProductHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularGLProductHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularGLProductMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularGLProductMap

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_entry
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_entry

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_lastRow
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_lastRow

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_lastColumn
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_lastColumn

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_dropLast
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_dropLast

#check @SerrePositivity.KST.ProExcision.triangularAction_dropLast_intertwining
#print axioms SerrePositivity.KST.ProExcision.triangularAction_dropLast_intertwining

#check @SerrePositivity.KST.ProExcision.triangularAction_lastColumn
#print axioms SerrePositivity.KST.ProExcision.triangularAction_lastColumn

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLColumnAction
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLColumnAction

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularAffineHatGLHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularAffineHatGLHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularAffineHatGLMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.triangularAffineHatGLMap

#check @SerrePositivity.KST.ProExcision.claim415FactorizationHom
#print axioms SerrePositivity.KST.ProExcision.claim415FactorizationHom

#check @SerrePositivity.KST.ProExcision.claim415FactorizationHom_base
#print axioms SerrePositivity.KST.ProExcision.claim415FactorizationHom_base

#check @SerrePositivity.KST.ProExcision.claim415FactorizationHom_fiber
#print axioms SerrePositivity.KST.ProExcision.claim415FactorizationHom_fiber

#check @SerrePositivity.KST.ProExcision.claim415FactorizationMap
#print axioms SerrePositivity.KST.ProExcision.claim415FactorizationMap

#check @SerrePositivity.KST.ProExcision.SimplicialActionPairMap
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionPairMap

#check @SerrePositivity.KST.ProExcision.SimplicialActionPairMap.comp
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionPairMap.comp

#check @SerrePositivity.KST.ProExcision.SimplicialActionHom.toPairMap
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionHom.toPairMap

#check @SerrePositivity.KST.ProExcision.relativeBarPairMap
#print axioms SerrePositivity.KST.ProExcision.relativeBarPairMap

#check @SerrePositivity.KST.ProExcision.relativeBarPairMap_comp
#print axioms SerrePositivity.KST.ProExcision.relativeBarPairMap_comp

#check @SerrePositivity.KST.ProExcision.relativeBarPairMap_toPairMap
#print axioms SerrePositivity.KST.ProExcision.relativeBarPairMap_toPairMap

#check @SerrePositivity.KST.ProExcision.simplicialActionProductLift
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductLift

#check @SerrePositivity.KST.ProExcision.simplicialActionProductLift_section
#print axioms SerrePositivity.KST.ProExcision.simplicialActionProductLift_section

#check @SerrePositivity.KST.ProExcision.claim415FactorizationMap_section
#print axioms SerrePositivity.KST.ProExcision.claim415FactorizationMap_section

#check @SerrePositivity.KST.ProExcision.claim415PairMap
#print axioms SerrePositivity.KST.ProExcision.claim415PairMap

#check @SerrePositivity.KST.ProExcision.claim415_factorized_relative_zero
#print axioms SerrePositivity.KST.ProExcision.claim415_factorized_relative_zero

#check @SerrePositivity.KST.ProExcision.columnBlockInclusion
#print axioms SerrePositivity.KST.ProExcision.columnBlockInclusion

#check @SerrePositivity.KST.ProExcision.columnBlockInclusion_left
#print axioms SerrePositivity.KST.ProExcision.columnBlockInclusion_left

#check @SerrePositivity.KST.ProExcision.columnBlockInclusion_right
#print axioms SerrePositivity.KST.ProExcision.columnBlockInclusion_right

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_mul_columnInclusion
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_mul_columnInclusion

#check @SerrePositivity.KST.ProExcision.matrixDropLast_one_add_lastColumn
#print axioms SerrePositivity.KST.ProExcision.matrixDropLast_one_add_lastColumn

#check @SerrePositivity.KST.ProExcision.matrixLastColumn_one_add_lastColumn
#print axioms SerrePositivity.KST.ProExcision.matrixLastColumn_one_add_lastColumn

#check @SerrePositivity.KST.ProExcision.columnBlockInclusion_coe
#print axioms SerrePositivity.KST.ProExcision.columnBlockInclusion_coe

#check @SerrePositivity.KST.ProExcision.idealColumnBlockInclusion_equivariant
#print axioms SerrePositivity.KST.ProExcision.idealColumnBlockInclusion_equivariant

#check @SerrePositivity.KST.ProExcision.lastRightColumn_dropLast
#print axioms SerrePositivity.KST.ProExcision.lastRightColumn_dropLast

#check @SerrePositivity.KST.ProExcision.lastRightColumn_lastColumn
#print axioms SerrePositivity.KST.ProExcision.lastRightColumn_lastColumn

#check @SerrePositivity.KST.ProExcision.claim415ColumnPairMap
#print axioms SerrePositivity.KST.ProExcision.claim415ColumnPairMap

#check @SerrePositivity.KST.ProExcision.claim415ColumnPairMap_base
#print axioms SerrePositivity.KST.ProExcision.claim415ColumnPairMap_base

#check @SerrePositivity.KST.ProExcision.claim415ColumnPairMap_fiber
#print axioms SerrePositivity.KST.ProExcision.claim415ColumnPairMap_fiber

#check @SerrePositivity.KST.ProExcision.claim415
#print axioms SerrePositivity.KST.ProExcision.claim415

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLRankSequence
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLRankSequence

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableHatGL
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableHatGL

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableHatGL_isGrouplike
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableHatGL_isGrouplike

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableHatGLInclusion
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableHatGLInclusion

#check @SerrePositivity.KST.ProExcision.SimplicialActionOverHom
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionOverHom

#check @SerrePositivity.KST.ProExcision.SimplicialActionOverHom.total
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionOverHom.total

#check @SerrePositivity.KST.ProExcision.SimplicialActionOverHom.toPairMap
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionOverHom.toPairMap

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.columnBlockMap
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.columnBlockMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnBlockOverHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnBlockOverHom

#check @SerrePositivity.KST.ProExcision.sequentialModule_representative
#print axioms SerrePositivity.KST.ProExcision.sequentialModule_representative

#check @SerrePositivity.KST.ProExcision.sequentialModule_map_zero
#print axioms SerrePositivity.KST.ProExcision.sequentialModule_map_zero

#check @SerrePositivity.KST.ProExcision.sequentialModule_map_injective_of_finite_iso
#print axioms SerrePositivity.KST.ProExcision.sequentialModule_map_injective_of_finite_iso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRankSequence
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRankSequence

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineColimit
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineColimit

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineInclusion
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineInclusion

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffine_representative
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffine_representative

#check @SerrePositivity.KST.ProExcision.blockUpperUnit
#print axioms SerrePositivity.KST.ProExcision.blockUpperUnit

#check @SerrePositivity.KST.ProExcision.blockLowerUnit
#print axioms SerrePositivity.KST.ProExcision.blockLowerUnit

#check @SerrePositivity.KST.ProExcision.whiteheadBlockFactorization
#print axioms SerrePositivity.KST.ProExcision.whiteheadBlockFactorization

#check @SerrePositivity.KST.ProExcision.relativeModuleMap_factor_of_zero
#print axioms SerrePositivity.KST.ProExcision.relativeModuleMap_factor_of_zero

#check @SerrePositivity.KST.ProExcision.relativeModuleMap_factor_of_split_square
#print axioms SerrePositivity.KST.ProExcision.relativeModuleMap_factor_of_split_square

#check @SerrePositivity.KST.ProExcision.splitRelative_action_image
#print axioms SerrePositivity.KST.ProExcision.splitRelative_action_image

#check @SerrePositivity.KST.ProExcision.columnBlockInclusion_zero
#print axioms SerrePositivity.KST.ProExcision.columnBlockInclusion_zero

#check @SerrePositivity.KST.ProExcision.columnBlockInclusion_succ
#print axioms SerrePositivity.KST.ProExcision.columnBlockInclusion_succ

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_zero
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_zero

#check @SerrePositivity.KST.ProExcision.firstBlockMatrix_succ
#print axioms SerrePositivity.KST.ProExcision.firstBlockMatrix_succ

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.columnRightMap
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.columnRightMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnRightActionHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnRightActionHom

#check @SerrePositivity.KST.ProExcision.SimplicialActionPairMap.ext_of_maps
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionPairMap.ext_of_maps

#check @SerrePositivity.KST.ProExcision.SimplicialActionPairMap.identity
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionPairMap.identity

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnBlockPair_zero
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnBlockPair_zero

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnBlockPair_succ
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnBlockPair_succ

#check @SerrePositivity.KST.ProExcision.relativeBarPairMap_identity
#print axioms SerrePositivity.KST.ProExcision.relativeBarPairMap_identity

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRankSequence_map
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRankSequence_map

#check @SerrePositivity.KST.ProExcision.idealVectorRightHom_columnBlock
#print axioms SerrePositivity.KST.ProExcision.idealVectorRightHom_columnBlock

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnRight_then_block
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnRight_then_block

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnRight_block_commute
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnRight_block_commute

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRightNatTrans
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRightNatTrans

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRightColimitMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRightColimitMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRight_leg_zero
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRight_leg_zero

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRightColimitMap_zero
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeAffineRightColimitMap_zero

#check @SerrePositivity.KST.ProExcision.integerUnitizationOpEquiv
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationOpEquiv

#check @SerrePositivity.KST.ProExcision.integerUnitizationOpEquiv_fst
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationOpEquiv_fst

#check @SerrePositivity.KST.ProExcision.integerUnitizationOpEquiv_inr
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationOpEquiv_inr

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.mulOpposite
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.mulOpposite

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.mulOppositeElement
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.mulOppositeElement

#check @SerrePositivity.KST.ProExcision.neg_one_pow_fin_rev
#print axioms SerrePositivity.KST.ProExcision.neg_one_pow_fin_rev

#check @SerrePositivity.KST.ProExcision.reversalChainSign
#print axioms SerrePositivity.KST.ProExcision.reversalChainSign

#check @SerrePositivity.KST.ProExcision.reversalChainSign_mul_self
#print axioms SerrePositivity.KST.ProExcision.reversalChainSign_mul_self

#check @SerrePositivity.KST.ProExcision.alternatingReversalDifferential
#print axioms SerrePositivity.KST.ProExcision.alternatingReversalDifferential

#check @SerrePositivity.KST.ProExcision.reversalChainComponentIso
#print axioms SerrePositivity.KST.ProExcision.reversalChainComponentIso

#check @SerrePositivity.KST.ProExcision.alternatingReversalMap
#print axioms SerrePositivity.KST.ProExcision.alternatingReversalMap

#check @SerrePositivity.KST.ProExcision.alternatingReversalIso
#print axioms SerrePositivity.KST.ProExcision.alternatingReversalIso

#check @SerrePositivity.KST.ProExcision.alternatingReversalIso_natural
#print axioms SerrePositivity.KST.ProExcision.alternatingReversalIso_natural

#check @SerrePositivity.KST.ProExcision.linearizedReversalIso
#print axioms SerrePositivity.KST.ProExcision.linearizedReversalIso

#check @SerrePositivity.KST.ProExcision.linearizedReversalIso_natural
#print axioms SerrePositivity.KST.ProExcision.linearizedReversalIso_natural

#check @SerrePositivity.KST.ProExcision.linearizedReversalChainIso
#print axioms SerrePositivity.KST.ProExcision.linearizedReversalChainIso

#check @SerrePositivity.KST.ProExcision.linearizedReversalChainIso_natural
#print axioms SerrePositivity.KST.ProExcision.linearizedReversalChainIso_natural

#check @SerrePositivity.KST.ProExcision.linearizedChainFunctor
#print axioms SerrePositivity.KST.ProExcision.linearizedChainFunctor

#check @SerrePositivity.KST.ProExcision.linearizedReversalChainNatIso
#print axioms SerrePositivity.KST.ProExcision.linearizedReversalChainNatIso

#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel.toNatIso
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel.toNatIso

#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel.reversalNatIso
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel.reversalNatIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverse
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverse

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOpposite
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOpposite

#check @SerrePositivity.KST.ProExcision.oppositeNerveSimplex
#print axioms SerrePositivity.KST.ProExcision.oppositeNerveSimplex

#check @SerrePositivity.KST.ProExcision.nerveOppositeSimplex
#print axioms SerrePositivity.KST.ProExcision.nerveOppositeSimplex

#check @SerrePositivity.KST.ProExcision.oppositeNerveSimplex_nerveOppositeSimplex
#print axioms SerrePositivity.KST.ProExcision.oppositeNerveSimplex_nerveOppositeSimplex

#check @SerrePositivity.KST.ProExcision.nerveOppositeSimplex_oppositeNerveSimplex
#print axioms SerrePositivity.KST.ProExcision.nerveOppositeSimplex_oppositeNerveSimplex

#check @SerrePositivity.KST.ProExcision.oppositeFunctorMap_heq
#print axioms SerrePositivity.KST.ProExcision.oppositeFunctorMap_heq

#check @SerrePositivity.KST.ProExcision.nerveOppositeMap
#print axioms SerrePositivity.KST.ProExcision.nerveOppositeMap

#check @SerrePositivity.KST.ProExcision.oppositeNerveSimplexEquiv
#print axioms SerrePositivity.KST.ProExcision.oppositeNerveSimplexEquiv

#check @SerrePositivity.KST.ProExcision.nerveOppositeIso
#print axioms SerrePositivity.KST.ProExcision.nerveOppositeIso

#check @SerrePositivity.KST.ProExcision.nerveOppositeIso_natural
#print axioms SerrePositivity.KST.ProExcision.nerveOppositeIso_natural

#check @SerrePositivity.KST.ProExcision.reversalEdge
#print axioms SerrePositivity.KST.ProExcision.reversalEdge

#check @SerrePositivity.KST.ProExcision.edgeToReversal
#print axioms SerrePositivity.KST.ProExcision.edgeToReversal

#check @SerrePositivity.KST.ProExcision.reversalComponentsMap
#print axioms SerrePositivity.KST.ProExcision.reversalComponentsMap

#check @SerrePositivity.KST.ProExcision.reversalComponentsEquiv
#print axioms SerrePositivity.KST.ProExcision.reversalComponentsEquiv

#check @SerrePositivity.KST.ProExcision.componentRingMap
#print axioms SerrePositivity.KST.ProExcision.componentRingMap

#check @SerrePositivity.KST.ProExcision.componentRingMap_mk
#print axioms SerrePositivity.KST.ProExcision.componentRingMap_mk

#check @SerrePositivity.KST.ProExcision.componentRingMap_id
#print axioms SerrePositivity.KST.ProExcision.componentRingMap_id

#check @SerrePositivity.KST.ProExcision.componentRingMap_comp
#print axioms SerrePositivity.KST.ProExcision.componentRingMap_comp

#check @SerrePositivity.KST.ProExcision.componentRingEquiv
#print axioms SerrePositivity.KST.ProExcision.componentRingEquiv

#check @SerrePositivity.KST.ProExcision.ringReversalComponentsEquiv
#print axioms SerrePositivity.KST.ProExcision.ringReversalComponentsEquiv

#check @SerrePositivity.KST.ProExcision.ringReversalComponentsEquiv_mk
#print axioms SerrePositivity.KST.ProExcision.ringReversalComponentsEquiv_mk

#check @SerrePositivity.KST.ProExcision.ringReversalComponentsEquiv_simplex
#print axioms SerrePositivity.KST.ProExcision.ringReversalComponentsEquiv_simplex

#check @SerrePositivity.KST.ProExcision.ringOppositeObject
#print axioms SerrePositivity.KST.ProExcision.ringOppositeObject

#check @SerrePositivity.KST.ProExcision.ringOppositeSpaceIso
#print axioms SerrePositivity.KST.ProExcision.ringOppositeSpaceIso

#check @SerrePositivity.KST.ProExcision.ringOppositeComponentsEquiv
#print axioms SerrePositivity.KST.ProExcision.ringOppositeComponentsEquiv

#check @SerrePositivity.KST.ProExcision.ringOppositeComponentsEquiv_simplex
#print axioms SerrePositivity.KST.ProExcision.ringOppositeComponentsEquiv_simplex

#check @SerrePositivity.KST.ProExcision.integerUnitizationOpEquiv_natural
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationOpEquiv_natural

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.unitizationOppositeIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.unitizationOppositeIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.unitizationReverseIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.unitizationReverseIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.unitizationReverseOppositeIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.unitizationReverseOppositeIso

#check @SerrePositivity.KST.ProExcision.componentRingMap_simplex
#print axioms SerrePositivity.KST.ProExcision.componentRingMap_simplex

#check @SerrePositivity.KST.ProExcision.componentRingEquiv_simplex
#print axioms SerrePositivity.KST.ProExcision.componentRingEquiv_simplex

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeComponentEquiv
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeComponentEquiv

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeComponentEquiv_simplex
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeComponentEquiv_simplex

#check @SerrePositivity.KST.ProExcision.integerUnitizationMatrixOpEquiv
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMatrixOpEquiv

#check @SerrePositivity.KST.ProExcision.integerUnitizationMatrixOpEquiv_fst
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMatrixOpEquiv_fst

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeMatrixComponentsEquiv
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeMatrixComponentsEquiv

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeMatrix_components
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeMatrix_components

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGL_mem_iff
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGL_mem_iff

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGLMulEquiv
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGLMulEquiv

#check @SerrePositivity.KST.ProExcision.monoidReverseOpposite
#print axioms SerrePositivity.KST.ProExcision.monoidReverseOpposite

#check @SerrePositivity.KST.ProExcision.monoidReverseOppositeMap
#print axioms SerrePositivity.KST.ProExcision.monoidReverseOppositeMap

#check @SerrePositivity.KST.ProExcision.integerUnitizationMatrixOpEquiv_natural
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMatrixOpEquiv_natural

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGL_natural
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGL_natural

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGLIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGLIso

#check @SerrePositivity.KST.ProExcision.singleObjOppositeFunctor
#print axioms SerrePositivity.KST.ProExcision.singleObjOppositeFunctor

#check @SerrePositivity.KST.ProExcision.singleObjUnopFunctor
#print axioms SerrePositivity.KST.ProExcision.singleObjUnopFunctor

#check @SerrePositivity.KST.ProExcision.singleObjOppositeFunctor_natural
#print axioms SerrePositivity.KST.ProExcision.singleObjOppositeFunctor_natural

#check @SerrePositivity.KST.ProExcision.singleObjOppositeNerveIso
#print axioms SerrePositivity.KST.ProExcision.singleObjOppositeNerveIso

#check @SerrePositivity.KST.ProExcision.singleObjOppositeNerveIso_natural
#print axioms SerrePositivity.KST.ProExcision.singleObjOppositeNerveIso_natural

#check @SerrePositivity.KST.ProExcision.monoidOppositeNerveIso
#print axioms SerrePositivity.KST.ProExcision.monoidOppositeNerveIso

#check @SerrePositivity.KST.ProExcision.monoidOppositeNerveIso_natural
#print axioms SerrePositivity.KST.ProExcision.monoidOppositeNerveIso_natural

#check @SerrePositivity.KST.ProExcision.bisimplicialBarReverseOppositeIso
#print axioms SerrePositivity.KST.ProExcision.bisimplicialBarReverseOppositeIso

#check @SerrePositivity.KST.ProExcision.monoidBarReverseOppositeIso
#print axioms SerrePositivity.KST.ProExcision.monoidBarReverseOppositeIso

#check @SerrePositivity.KST.ProExcision.monoidBarReverseOppositeIso_natural
#print axioms SerrePositivity.KST.ProExcision.monoidBarReverseOppositeIso_natural

#check @SerrePositivity.KST.ProExcision.monoidBarIso
#print axioms SerrePositivity.KST.ProExcision.monoidBarIso

#check @SerrePositivity.KST.ProExcision.monoidBarReverseOppositeHomologyIso
#print axioms SerrePositivity.KST.ProExcision.monoidBarReverseOppositeHomologyIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGLBarIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGLBarIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGLHomologyIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeHatGLHomologyIso

#check @SerrePositivity.KST.ProExcision.idealRowMatrixVecHom
#print axioms SerrePositivity.KST.ProExcision.idealRowMatrixVecHom

#check @SerrePositivity.KST.ProExcision.idealRowMatrixAction
#print axioms SerrePositivity.KST.ProExcision.idealRowMatrixAction

#check @SerrePositivity.KST.ProExcision.idealRowMatrixAction_functorial
#print axioms SerrePositivity.KST.ProExcision.idealRowMatrixAction_functorial

#check @SerrePositivity.KST.ProExcision.monCatOpposite
#print axioms SerrePositivity.KST.ProExcision.monCatOpposite

#check @SerrePositivity.KST.ProExcision.monoidOpposite
#print axioms SerrePositivity.KST.ProExcision.monoidOpposite

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLRowAction
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.hatGLRowAction

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffine
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffine

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineBase
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineBase

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineFiber
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineFiber

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffine_mul_fiber
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffine_mul_fiber

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealOpAddEquiv
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealOpAddEquiv

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealOpAddEquiv_coe
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealOpAddEquiv_coe

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealOpAddEquiv_natural
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealOpAddEquiv_natural

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVectorAddEquiv
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVectorAddEquiv

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVectorMulEquiv
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVectorMulEquiv

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVector_equivariant
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVector_equivariant

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVectorMulEquiv_natural
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVectorMulEquiv_natural

#check @SerrePositivity.KST.ProExcision.actionProductMulEquiv
#print axioms SerrePositivity.KST.ProExcision.actionProductMulEquiv

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeColumnRowMulEquiv
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeColumnRowMulEquiv

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineMulEquiv
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineMulEquiv

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineBarIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineBarIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineSection
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineSection

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineIso_section
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineIso_section

#check @SerrePositivity.KST.ProExcision.relativeModuleMap_id
#print axioms SerrePositivity.KST.ProExcision.relativeModuleMap_id

#check @SerrePositivity.KST.ProExcision.relativeSquare_inverse
#print axioms SerrePositivity.KST.ProExcision.relativeSquare_inverse

#check @SerrePositivity.KST.ProExcision.relativeModuleIso
#print axioms SerrePositivity.KST.ProExcision.relativeModuleIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineBarIso_section
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineBarIso_section

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso_section
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso_section

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineModule
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineModule

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeRelativeAffineIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeRelativeAffineIso

#check @SerrePositivity.KST.ProExcision.idealLeftMultiplication
#print axioms SerrePositivity.KST.ProExcision.idealLeftMultiplication

#check @SerrePositivity.KST.ProExcision.idealVectorLeftHom
#print axioms SerrePositivity.KST.ProExcision.idealVectorLeftHom

#check @SerrePositivity.KST.ProExcision.idealVectorLeftHom_equivariant
#print axioms SerrePositivity.KST.ProExcision.idealVectorLeftHom_equivariant

#check @SerrePositivity.KST.ProExcision.idealVectorLeftHom_functorial
#print axioms SerrePositivity.KST.ProExcision.idealVectorLeftHom_functorial

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.vertexValue
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.vertexValue

#check @SerrePositivity.KST.ProExcision.simplexVertexMap_rev
#print axioms SerrePositivity.KST.ProExcision.simplexVertexMap_rev

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOpposite_vertexValue
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOpposite_vertexValue

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.standardVertexElement_coe
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.standardVertexElement_coe

#check @SerrePositivity.KST.ProExcision.isCentralElement_op
#print axioms SerrePositivity.KST.ProExcision.isCentralElement_op

#check @SerrePositivity.KST.ProExcision.SimplicialIdealData.rowLeftMap
#print axioms SerrePositivity.KST.ProExcision.SimplicialIdealData.rowLeftMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowLeftActionHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowLeftActionHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftMap_section
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftMap_section

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVector_right_left
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVector_right_left

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeStandardVertex
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeStandardVertex

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineIso_multiplication
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineIso_multiplication

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineBarIso_multiplication
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineBarIso_multiplication

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso_multiplication
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso_multiplication

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeRelativeAffineIso_multiplication
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeRelativeAffineIso_multiplication

#check @SerrePositivity.KST.ProExcision.idealRowBlockInclusion_equivariant
#print axioms SerrePositivity.KST.ProExcision.idealRowBlockInclusion_equivariant

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowBlockOverHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowBlockOverHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineBlockMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineBlockMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineBlockMap_section
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineBlockMap_section

#check @SerrePositivity.KST.ProExcision.integerUnitizationMatrixOpEquiv_block
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMatrixOpEquiv_block

#check @SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVector_block
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationIdealOpVector_block

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineIso_block
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineIso_block

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineBarIso_block
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineBarIso_block

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso_block
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso_block

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineBlockMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineBlockMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeRelativeAffineIso_block
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.reverseOppositeRelativeAffineIso_block

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeft_then_block_zero
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeft_then_block_zero

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineRankSequence
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineRankSequence

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineColimit
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineColimit

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineInclusion
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineInclusion

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineComparisonNatIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineComparisonNatIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineRankSequence_map
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineRankSequence_map

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftNatTrans
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftNatTrans

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftNatTrans_app
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftNatTrans_app

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftColimitMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftColimitMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeft_leg_zero
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeft_leg_zero

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftColimitMap_zero
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.relativeRowAffineLeftColimitMap_zero

#check @SerrePositivity.KST.ProExcision.finitePower_preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.finitePower_preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.monoidBarFunctor
#print axioms SerrePositivity.KST.ProExcision.monoidBarFunctor

#check @SerrePositivity.KST.ProExcision.monoidBarDegreeIso
#print axioms SerrePositivity.KST.ProExcision.monoidBarDegreeIso

#check @SerrePositivity.KST.ProExcision.monoidBarFunctor_preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.monoidBarFunctor_preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.monoidBarSequentialColimitIso
#print axioms SerrePositivity.KST.ProExcision.monoidBarSequentialColimitIso

#check @SerrePositivity.KST.ProExcision.abelianShortHomology_preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.abelianShortHomology_preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.intForgetShortComplex_preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.intForgetShortComplex_preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.moduleShortHomology_preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.moduleShortHomology_preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.moduleShortComplexFunctor_preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.moduleShortComplexFunctor_preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.moduleChainHomology_preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.moduleChainHomology_preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.integerLinearizationHomEquiv
#print axioms SerrePositivity.KST.ProExcision.integerLinearizationHomEquiv

#check @SerrePositivity.KST.ProExcision.integerLinearizationAdjunction
#print axioms SerrePositivity.KST.ProExcision.integerLinearizationAdjunction

#check @SerrePositivity.KST.ProExcision.integerLinearization_preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.integerLinearization_preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.linearizedChainEvaluationIso
#print axioms SerrePositivity.KST.ProExcision.linearizedChainEvaluationIso

#check @SerrePositivity.KST.ProExcision.linearizedChainFunctor_preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.linearizedChainFunctor_preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel.preservesSequentialColimits
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel.preservesSequentialColimits

#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel.sequentialColimitIso
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel.sequentialColimitIso

#check @SerrePositivity.KST.ProExcision.relativeModuleDiagram
#print axioms SerrePositivity.KST.ProExcision.relativeModuleDiagram

#check @SerrePositivity.KST.ProExcision.relativeModuleDiagramProjection
#print axioms SerrePositivity.KST.ProExcision.relativeModuleDiagramProjection

#check @SerrePositivity.KST.ProExcision.relativeModuleDiagramProjection_condition
#print axioms SerrePositivity.KST.ProExcision.relativeModuleDiagramProjection_condition

#check @SerrePositivity.KST.ProExcision.relativeModuleDiagramCofork
#print axioms SerrePositivity.KST.ProExcision.relativeModuleDiagramCofork

#check @SerrePositivity.KST.ProExcision.relativeModuleDiagramIsCokernel
#print axioms SerrePositivity.KST.ProExcision.relativeModuleDiagramIsCokernel

#check @SerrePositivity.KST.ProExcision.relativeModuleSequentialColimitIso
#print axioms SerrePositivity.KST.ProExcision.relativeModuleSequentialColimitIso

#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel.barSequentialColimitIso
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel.barSequentialColimitIso

#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel.barSequentialColimitIso_natural
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel.barSequentialColimitIso_natural

#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel.relativeBarSequentialColimitIso
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel.relativeBarSequentialColimitIso

#check @SerrePositivity.KST.ProExcision.relativeModuleMap_projection
#print axioms SerrePositivity.KST.ProExcision.relativeModuleMap_projection

#check @SerrePositivity.KST.ProExcision.relativeModuleDiagramMap
#print axioms SerrePositivity.KST.ProExcision.relativeModuleDiagramMap

#check @SerrePositivity.KST.ProExcision.relativeModuleDiagramMap_projection
#print axioms SerrePositivity.KST.ProExcision.relativeModuleDiagramMap_projection

#check @SerrePositivity.KST.ProExcision.relativeModuleSequentialColimitIso_projection
#print axioms SerrePositivity.KST.ProExcision.relativeModuleSequentialColimitIso_projection

#check @SerrePositivity.KST.ProExcision.relativeModuleSequentialMap
#print axioms SerrePositivity.KST.ProExcision.relativeModuleSequentialMap

#check @SerrePositivity.KST.ProExcision.relativeModuleSequentialColimitIso_natural
#print axioms SerrePositivity.KST.ProExcision.relativeModuleSequentialColimitIso_natural

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRankSequence
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRankSequence

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineSectionNatTrans
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineSectionNatTrans

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffine
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffine

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineSection
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineSection

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRightNatTrans
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRightNatTrans

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRightMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRightMap

#check @SerrePositivity.KST.ProExcision.relativeStableBarMap
#print axioms SerrePositivity.KST.ProExcision.relativeStableBarMap

#check @SerrePositivity.KST.ProExcision.finiteBarHomologySquare
#print axioms SerrePositivity.KST.ProExcision.finiteBarHomologySquare

#check @SerrePositivity.KST.ProExcision.SimplicialHomologyModel.relativeBarSequentialColimitIso_natural
#print axioms SerrePositivity.KST.ProExcision.SimplicialHomologyModel.relativeBarSequentialColimitIso_natural

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRelativeDiagramIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRelativeDiagramIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeModule
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeModule

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRightNatTrans_section
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRightNatTrans_section

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRightRelativeDiagramMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRightRelativeDiagramMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRelativeDiagramIso_right
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.columnAffineRelativeDiagramIso_right

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeRightMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeRightMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeIso_right
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeIso_right

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeRightMap_zero
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableColumnAffineRelativeRightMap_zero

#check @SerrePositivity.KST.ProExcision.idealVectorLeftHom_block
#print axioms SerrePositivity.KST.ProExcision.idealVectorLeftHom_block

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeft_block_commute
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeft_block_commute

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineRankSequence
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineRankSequence

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineSectionNatTrans
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineSectionNatTrans

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffine
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffine

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineSection
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineSection

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftNatTrans
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftNatTrans

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineLeftMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineLeftMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineRelativeDiagramIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineRelativeDiagramIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeModule
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeModule

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftNatTrans_section
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftNatTrans_section

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftRelativeDiagramMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineLeftRelativeDiagramMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineRelativeDiagramIso_left
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.rowAffineRelativeDiagramIso_left

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeLeftMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeLeftMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeIso_left
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeIso_left

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeLeftMap_zero
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.stableRowAffineRelativeLeftMap_zero

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.unitizationMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.unitizationMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.matrix_components
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.matrix_components

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.hatGLHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.hatGLHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.hatGLMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.hatGLMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.vertexValue_natural
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.vertexValue_natural

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdeal
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdeal

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealInclusion
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealInclusion

#check @SerrePositivity.KST.ProExcision.centralMultiplicationAddHom
#print axioms SerrePositivity.KST.ProExcision.centralMultiplicationAddHom

#check @SerrePositivity.KST.ProExcision.centralMultiplicationAddEquiv
#print axioms SerrePositivity.KST.ProExcision.centralMultiplicationAddEquiv

#check @SerrePositivity.KST.ProExcision.centralMultiplicationAddEquiv_coe_right
#print axioms SerrePositivity.KST.ProExcision.centralMultiplicationAddEquiv_coe_right

#check @SerrePositivity.KST.ProExcision.centralMultiplicationAddEquiv_natural
#print axioms SerrePositivity.KST.ProExcision.centralMultiplicationAddEquiv_natural

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.columnGroupMap
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.columnGroupMap

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.columnActionOverHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.columnActionOverHom

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.rowActionOverHom
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.rowActionOverHom

#check @SerrePositivity.KST.ProExcision.integerUnitizationMap_injective
#print axioms SerrePositivity.KST.ProExcision.integerUnitizationMap_injective

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.columnGroupMap_injective
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRingHom.columnGroupMap_injective

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealKernelAddEquiv
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealKernelAddEquiv

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealKernelAddEquiv_inclusion
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealKernelAddEquiv_inclusion

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealKernelAddEquiv_natural
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealKernelAddEquiv_natural

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealKernelVectorAddEquiv
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealKernelVectorAddEquiv

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealColumnGroupIso
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealColumnGroupIso

#check @SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealColumnGroupIso_inclusion
#print axioms SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing.centralIdealColumnGroupIso_inclusion

#check @SerrePositivity.KST.ProExcision.SimplicialActionHom.ofInjectiveComposite
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionHom.ofInjectiveComposite

#check @SerrePositivity.KST.ProExcision.SimplicialActionHom.inverseOfIso
#print axioms SerrePositivity.KST.ProExcision.SimplicialActionHom.inverseOfIso

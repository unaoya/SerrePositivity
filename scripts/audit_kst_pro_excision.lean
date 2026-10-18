import SerrePositivity.KST.ProExcision
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

#check @SerrePositivity.KST.ProExcision.integerLinearization
#print axioms SerrePositivity.KST.ProExcision.integerLinearization
#check @SerrePositivity.KST.ProExcision.integerGenerator
#print axioms SerrePositivity.KST.ProExcision.integerGenerator
#check @SerrePositivity.KST.ProExcision.integerLinearization_map_generator
#print axioms SerrePositivity.KST.ProExcision.integerLinearization_map_generator
#check @SerrePositivity.KST.ProExcision.integerLinearization_hom_ext
#print axioms SerrePositivity.KST.ProExcision.integerLinearization_hom_ext
#check @SerrePositivity.KST.ProExcision.linearizedSpace
#print axioms SerrePositivity.KST.ProExcision.linearizedSpace
#check @SerrePositivity.KST.ProExcision.linearizedSpaceMap
#print axioms SerrePositivity.KST.ProExcision.linearizedSpaceMap
#check @SerrePositivity.KST.ProExcision.linearizedSpaceHomotopy
#print axioms SerrePositivity.KST.ProExcision.linearizedSpaceHomotopy
#check @SerrePositivity.KST.ProExcision.integerTensor
#print axioms SerrePositivity.KST.ProExcision.integerTensor
#check @SerrePositivity.KST.ProExcision.integerTensorMap
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap
#check @SerrePositivity.KST.ProExcision.integerTensor_hom_ext
#print axioms SerrePositivity.KST.ProExcision.integerTensor_hom_ext
#check @SerrePositivity.KST.ProExcision.integerTensorIso
#print axioms SerrePositivity.KST.ProExcision.integerTensorIso
#check @SerrePositivity.KST.ProExcision.integerTensorIso_generator
#print axioms SerrePositivity.KST.ProExcision.integerTensorIso_generator
#check @SerrePositivity.KST.ProExcision.integerTensorIso_naturality
#print axioms SerrePositivity.KST.ProExcision.integerTensorIso_naturality
#check @SerrePositivity.KST.ProExcision.simplicialIntegerTensor
#print axioms SerrePositivity.KST.ProExcision.simplicialIntegerTensor
#check @SerrePositivity.KST.ProExcision.linearizedTensorComparison
#print axioms SerrePositivity.KST.ProExcision.linearizedTensorComparison
#check @SerrePositivity.KST.ProExcision.linearizedTensorIso
#print axioms SerrePositivity.KST.ProExcision.linearizedTensorIso
#check @SerrePositivity.KST.ProExcision.linearizedCylinder
#print axioms SerrePositivity.KST.ProExcision.linearizedCylinder
#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₀
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₀
#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₁
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₁
#check @SerrePositivity.KST.ProExcision.LinearizedHomotopy
#print axioms SerrePositivity.KST.ProExcision.LinearizedHomotopy
#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy
#check @SerrePositivity.KST.ProExcision.LinearizedHomotopy.truncate
#print axioms SerrePositivity.KST.ProExcision.LinearizedHomotopy.truncate
#check @SerrePositivity.KST.ProExcision.linearizedTensorHomotopy
#print axioms SerrePositivity.KST.ProExcision.linearizedTensorHomotopy
#check @SerrePositivity.KST.ProExcision.linearizedCylinderProjection
#print axioms SerrePositivity.KST.ProExcision.linearizedCylinderProjection
#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₀_projection
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₀_projection
#check @SerrePositivity.KST.ProExcision.linearizedEndpoint₁_projection
#print axioms SerrePositivity.KST.ProExcision.linearizedEndpoint₁_projection
#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.cancel_augmentation
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.cancel_augmentation
#check @SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy
#print axioms SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy

#check @SerrePositivity.KST.ProExcision.simplicialIntegerTensorMap
#print axioms SerrePositivity.KST.ProExcision.simplicialIntegerTensorMap
#check @SerrePositivity.KST.ProExcision.linearizedTensorIso_naturality
#print axioms SerrePositivity.KST.ProExcision.linearizedTensorIso_naturality
#check @SerrePositivity.KST.ProExcision.conjugationInterval_naturality
#print axioms SerrePositivity.KST.ProExcision.conjugationInterval_naturality
#check @SerrePositivity.KST.ProExcision.conjugationNerveHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.conjugationNerveHomotopy_naturality
#check @SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy_naturality
#print axioms SerrePositivity.KST.ProExcision.conjugationLinearizedHomotopy_naturality
#check @SerrePositivity.KST.ProExcision.homologyMap_eq_of_component_eq
#print axioms SerrePositivity.KST.ProExcision.homologyMap_eq_of_component_eq
#check @SerrePositivity.KST.ProExcision.geometricCylinderHomotopy
#print axioms SerrePositivity.KST.ProExcision.geometricCylinderHomotopy
#check @SerrePositivity.KST.ProExcision.linearizedCylinderHomotopy
#print axioms SerrePositivity.KST.ProExcision.linearizedCylinderHomotopy
#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.endpointChainHomotopy
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.endpointChainHomotopy
#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.homologyMap_eq
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.homologyMap_eq
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
#check @SerrePositivity.KST.ProExcision.integerLinearizationDesc
#print axioms SerrePositivity.KST.ProExcision.integerLinearizationDesc
#check @SerrePositivity.KST.ProExcision.integerLinearizationDesc_generator
#print axioms SerrePositivity.KST.ProExcision.integerLinearizationDesc_generator
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

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictifiedMap
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictifiedMap
#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictifiedMap_eq_low
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictifiedMap_eq_low
#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictifiedDifference_eq_zero
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictifiedDifference_eq_zero
#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictificationHomotopy
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.strictificationHomotopy
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

#check @SerrePositivity.KST.ProExcision.normalizedMap_component_eq
#print axioms SerrePositivity.KST.ProExcision.normalizedMap_component_eq

#check @SerrePositivity.KST.ProExcision.normalizedMap_eq_retract
#print axioms SerrePositivity.KST.ProExcision.normalizedMap_eq_retract

#check @SerrePositivity.KST.ProExcision.normalizedChainHomotopy
#print axioms SerrePositivity.KST.ProExcision.normalizedChainHomotopy

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.normalized_strictifiedMap_eq_low
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.normalized_strictifiedMap_eq_low

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.normalized_strictifiedDifference_eq_zero
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.normalized_strictifiedDifference_eq_zero

#check @SerrePositivity.KST.ProExcision.LinearizedMHomotopy.normalizedStrictificationHomotopy
#print axioms SerrePositivity.KST.ProExcision.LinearizedMHomotopy.normalizedStrictificationHomotopy

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

#check @SerrePositivity.KST.ProExcision.integerTensorMap_comp
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_comp

#check @SerrePositivity.KST.ProExcision.integerTensorMap_id
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_id

#check @SerrePositivity.KST.ProExcision.integerTensorMap_add_left
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_add_left

#check @SerrePositivity.KST.ProExcision.integerTensorMap_add_right
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_add_right

#check @SerrePositivity.KST.ProExcision.integerTensorRight
#print axioms SerrePositivity.KST.ProExcision.integerTensorRight

#check @SerrePositivity.KST.ProExcision.integerTensorRight_additive
#print axioms SerrePositivity.KST.ProExcision.integerTensorRight_additive

#check @SerrePositivity.KST.ProExcision.integerTensorBifunctor
#print axioms SerrePositivity.KST.ProExcision.integerTensorBifunctor

#check @SerrePositivity.KST.ProExcision.integerTensorBifunctor_additive
#print axioms SerrePositivity.KST.ProExcision.integerTensorBifunctor_additive

#check @SerrePositivity.KST.ProExcision.integerTensorBifunctor_obj_additive
#print axioms SerrePositivity.KST.ProExcision.integerTensorBifunctor_obj_additive

#check @SerrePositivity.KST.ProExcision.chainIntegerTensor_hasTotal
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensor_hasTotal

#check @SerrePositivity.KST.ProExcision.chainIntegerTensor
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensor

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorMap
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorMap

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorMap_eq_zero_low
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorMap_eq_zero_low

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorMap_sub_left
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorMap_sub_left

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorMap_sub_right
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorMap_sub_right

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorMap_augmentation_expansion
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorMap_augmentation_expansion

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorMap_augmentation_eq_low
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorMap_augmentation_eq_low

#check @SerrePositivity.KST.ProExcision.normalizedStrictifiedTensor_eq_low
#print axioms SerrePositivity.KST.ProExcision.normalizedStrictifiedTensor_eq_low

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

#check @SerrePositivity.KST.ProExcision.awFront
#print axioms SerrePositivity.KST.ProExcision.awFront

#check @SerrePositivity.KST.ProExcision.awBack
#print axioms SerrePositivity.KST.ProExcision.awBack

#check @SerrePositivity.KST.ProExcision.awFront_apply
#print axioms SerrePositivity.KST.ProExcision.awFront_apply

#check @SerrePositivity.KST.ProExcision.awBack_apply
#print axioms SerrePositivity.KST.ProExcision.awBack_apply

#check @SerrePositivity.KST.ProExcision.awDegrees
#print axioms SerrePositivity.KST.ProExcision.awDegrees

#check @SerrePositivity.KST.ProExcision.alexanderWhitneySummand
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitneySummand

#check @SerrePositivity.KST.ProExcision.alexanderWhitneyApp
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitneyApp

#check @SerrePositivity.KST.ProExcision.ι_chainIntegerTensorMap
#print axioms SerrePositivity.KST.ProExcision.ι_chainIntegerTensorMap

#check @SerrePositivity.KST.ProExcision.alexanderWhitneySummand_naturality
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitneySummand_naturality

#check @SerrePositivity.KST.ProExcision.alexanderWhitneyApp_naturality
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitneyApp_naturality

#check @SerrePositivity.KST.ProExcision.awInterval
#print axioms SerrePositivity.KST.ProExcision.awInterval

#check @SerrePositivity.KST.ProExcision.awInterval_apply
#print axioms SerrePositivity.KST.ProExcision.awInterval_apply

#check @SerrePositivity.KST.ProExcision.awFace_apply
#print axioms SerrePositivity.KST.ProExcision.awFace_apply

#check @SerrePositivity.KST.ProExcision.awInterval_face_before
#print axioms SerrePositivity.KST.ProExcision.awInterval_face_before

#check @SerrePositivity.KST.ProExcision.awInterval_face_after
#print axioms SerrePositivity.KST.ProExcision.awInterval_face_after

#check @SerrePositivity.KST.ProExcision.awInterval_face_inside
#print axioms SerrePositivity.KST.ProExcision.awInterval_face_inside

#check @SerrePositivity.KST.ProExcision.awFront_eq_interval
#print axioms SerrePositivity.KST.ProExcision.awFront_eq_interval

#check @SerrePositivity.KST.ProExcision.awBack_eq_interval
#print axioms SerrePositivity.KST.ProExcision.awBack_eq_interval

#check @SerrePositivity.KST.ProExcision.AWLeftIndex
#print axioms SerrePositivity.KST.ProExcision.AWLeftIndex

#check @SerrePositivity.KST.ProExcision.AWRightIndex
#print axioms SerrePositivity.KST.ProExcision.AWRightIndex

#check @SerrePositivity.KST.ProExcision.awBoundaryIndexForward
#print axioms SerrePositivity.KST.ProExcision.awBoundaryIndexForward

#check @SerrePositivity.KST.ProExcision.awBoundaryIndexInverse
#print axioms SerrePositivity.KST.ProExcision.awBoundaryIndexInverse

#check @SerrePositivity.KST.ProExcision.awBoundaryIndexEquiv
#print axioms SerrePositivity.KST.ProExcision.awBoundaryIndexEquiv

#check @SerrePositivity.KST.ProExcision.awBoundaryIndex_sum
#print axioms SerrePositivity.KST.ProExcision.awBoundaryIndex_sum

#check @SerrePositivity.KST.ProExcision.integerTensorMap_zero_left
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_zero_left

#check @SerrePositivity.KST.ProExcision.integerTensorMap_zero_right
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_zero_right

#check @SerrePositivity.KST.ProExcision.integerTensorMapLeftAddHom
#print axioms SerrePositivity.KST.ProExcision.integerTensorMapLeftAddHom

#check @SerrePositivity.KST.ProExcision.integerTensorMapRightAddHom
#print axioms SerrePositivity.KST.ProExcision.integerTensorMapRightAddHom

#check @SerrePositivity.KST.ProExcision.integerTensorMap_sum_left
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_sum_left

#check @SerrePositivity.KST.ProExcision.integerTensorMap_sum_right
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_sum_right

#check @SerrePositivity.KST.ProExcision.integerTensorMap_zsmul_left
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_zsmul_left

#check @SerrePositivity.KST.ProExcision.integerTensorMap_zsmul_right
#print axioms SerrePositivity.KST.ProExcision.integerTensorMap_zsmul_right

#check @SerrePositivity.KST.ProExcision.awTensorTerm
#print axioms SerrePositivity.KST.ProExcision.awTensorTerm

#check @SerrePositivity.KST.ProExcision.awTensorTerm_D₁
#print axioms SerrePositivity.KST.ProExcision.awTensorTerm_D₁

#check @SerrePositivity.KST.ProExcision.awTensorTerm_D₂
#print axioms SerrePositivity.KST.ProExcision.awTensorTerm_D₂

#check @SerrePositivity.KST.ProExcision.awTensorTerm_zero_D₁
#print axioms SerrePositivity.KST.ProExcision.awTensorTerm_zero_D₁

#check @SerrePositivity.KST.ProExcision.awTensorTerm_zero_D₂
#print axioms SerrePositivity.KST.ProExcision.awTensorTerm_zero_D₂

#check @SerrePositivity.KST.ProExcision.awTensorTerm_source_face
#print axioms SerrePositivity.KST.ProExcision.awTensorTerm_source_face

#check @SerrePositivity.KST.ProExcision.awInterval_face_last
#print axioms SerrePositivity.KST.ProExcision.awInterval_face_last

#check @SerrePositivity.KST.ProExcision.awInterval_face_zero
#print axioms SerrePositivity.KST.ProExcision.awInterval_face_zero

#check @SerrePositivity.KST.ProExcision.awDiagonal_sign_cancel
#print axioms SerrePositivity.KST.ProExcision.awDiagonal_sign_cancel

#check @SerrePositivity.KST.ProExcision.alexanderWhitney_source_boundary
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitney_source_boundary

#check @SerrePositivity.KST.ProExcision.awTensorTerm_interval_congr
#print axioms SerrePositivity.KST.ProExcision.awTensorTerm_interval_congr

#check @SerrePositivity.KST.ProExcision.alexanderWhitneySummand_succ_D₁
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitneySummand_succ_D₁

#check @SerrePositivity.KST.ProExcision.alexanderWhitney_horizontal_boundary
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitney_horizontal_boundary

#check @SerrePositivity.KST.ProExcision.alexanderWhitneySummand_castSucc_D₂
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitneySummand_castSucc_D₂

#check @SerrePositivity.KST.ProExcision.alexanderWhitney_vertical_boundary
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitney_vertical_boundary

#check @SerrePositivity.KST.ProExcision.awLeftBoundaryCoordinates
#print axioms SerrePositivity.KST.ProExcision.awLeftBoundaryCoordinates

#check @SerrePositivity.KST.ProExcision.awRightBoundaryCoordinates
#print axioms SerrePositivity.KST.ProExcision.awRightBoundaryCoordinates

#check @SerrePositivity.KST.ProExcision.awLeftBoundaryTerm
#print axioms SerrePositivity.KST.ProExcision.awLeftBoundaryTerm

#check @SerrePositivity.KST.ProExcision.awRightBoundaryTerm
#print axioms SerrePositivity.KST.ProExcision.awRightBoundaryTerm

#check @SerrePositivity.KST.ProExcision.awDiagonalBoundaryTerm
#print axioms SerrePositivity.KST.ProExcision.awDiagonalBoundaryTerm

#check @SerrePositivity.KST.ProExcision.awBoundaryCoordinates_sum
#print axioms SerrePositivity.KST.ProExcision.awBoundaryCoordinates_sum

#check @SerrePositivity.KST.ProExcision.awHorizontalFaceTerm
#print axioms SerrePositivity.KST.ProExcision.awHorizontalFaceTerm

#check @SerrePositivity.KST.ProExcision.awVerticalFaceTerm
#print axioms SerrePositivity.KST.ProExcision.awVerticalFaceTerm

#check @SerrePositivity.KST.ProExcision.awDeletedFaceTerm
#print axioms SerrePositivity.KST.ProExcision.awDeletedFaceTerm

#check @SerrePositivity.KST.ProExcision.awCutDiagonalTerm
#print axioms SerrePositivity.KST.ProExcision.awCutDiagonalTerm

#check @SerrePositivity.KST.ProExcision.awHorizontalFaceTerm_eq
#print axioms SerrePositivity.KST.ProExcision.awHorizontalFaceTerm_eq

#check @SerrePositivity.KST.ProExcision.awHorizontalFaceTerm_nonDiagonal
#print axioms SerrePositivity.KST.ProExcision.awHorizontalFaceTerm_nonDiagonal

#check @SerrePositivity.KST.ProExcision.awVerticalFaceTerm_nonDiagonal
#print axioms SerrePositivity.KST.ProExcision.awVerticalFaceTerm_nonDiagonal

#check @SerrePositivity.KST.ProExcision.awHorizontalFaceTerm_diagonal
#print axioms SerrePositivity.KST.ProExcision.awHorizontalFaceTerm_diagonal

#check @SerrePositivity.KST.ProExcision.awVerticalFaceTerm_diagonal
#print axioms SerrePositivity.KST.ProExcision.awVerticalFaceTerm_diagonal

#check @SerrePositivity.KST.ProExcision.awHorizontal_boundary_model
#print axioms SerrePositivity.KST.ProExcision.awHorizontal_boundary_model

#check @SerrePositivity.KST.ProExcision.awVertical_boundary_model
#print axioms SerrePositivity.KST.ProExcision.awVertical_boundary_model

#check @SerrePositivity.KST.ProExcision.awHorizontal_sum_split
#print axioms SerrePositivity.KST.ProExcision.awHorizontal_sum_split

#check @SerrePositivity.KST.ProExcision.awVertical_sum_split
#print axioms SerrePositivity.KST.ProExcision.awVertical_sum_split

#check @SerrePositivity.KST.ProExcision.alexanderWhitney_comm
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitney_comm

#check @SerrePositivity.KST.ProExcision.alexanderWhitney
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitney

#check @SerrePositivity.KST.ProExcision.alexanderWhitney_naturality
#print axioms SerrePositivity.KST.ProExcision.alexanderWhitney_naturality

#check @SerrePositivity.KST.ProExcision.chainIntegerTensorMap_comp
#print axioms SerrePositivity.KST.ProExcision.chainIntegerTensorMap_comp

#check @SerrePositivity.KST.ProExcision.normalizedAlexanderWhitney
#print axioms SerrePositivity.KST.ProExcision.normalizedAlexanderWhitney

#check @SerrePositivity.KST.ProExcision.normalizedAlexanderWhitney_naturality
#print axioms SerrePositivity.KST.ProExcision.normalizedAlexanderWhitney_naturality

#check @SerrePositivity.KST.ProExcision.ShuffleIndex
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.compl_card
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.compl_card

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.left
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.left

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.right
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.right

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.inversions
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.inversions

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.left_apply
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.left_apply

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.right_apply
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.right_apply

#check @SerrePositivity.KST.ProExcision.shuffleBidegree
#print axioms SerrePositivity.KST.ProExcision.shuffleBidegree

#check @SerrePositivity.KST.ProExcision.shuffleApp
#print axioms SerrePositivity.KST.ProExcision.shuffleApp

#check @SerrePositivity.KST.ProExcision.ι_shuffleApp
#print axioms SerrePositivity.KST.ProExcision.ι_shuffleApp

#check @SerrePositivity.KST.ProExcision.shuffleBidegree_naturality
#print axioms SerrePositivity.KST.ProExcision.shuffleBidegree_naturality

#check @SerrePositivity.KST.ProExcision.shuffleApp_naturality
#print axioms SerrePositivity.KST.ProExcision.shuffleApp_naturality

#check @SerrePositivity.KST.ProExcision.shufflePrefix_card
#print axioms SerrePositivity.KST.ProExcision.shufflePrefix_card

#check @SerrePositivity.KST.ProExcision.shufflePrefix_partition
#print axioms SerrePositivity.KST.ProExcision.shufflePrefix_partition

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.coordinates_add
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.coordinates_add

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.left_zero
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.left_zero

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.right_zero
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.right_zero

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.left_last
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.left_last

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.right_last
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.right_last

#check @SerrePositivity.KST.ProExcision.shufflePrefix_succ
#print axioms SerrePositivity.KST.ProExcision.shufflePrefix_succ

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.left_step
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.left_step

#check @SerrePositivity.KST.ProExcision.ShuffleIndex.right_step
#print axioms SerrePositivity.KST.ProExcision.ShuffleIndex.right_step

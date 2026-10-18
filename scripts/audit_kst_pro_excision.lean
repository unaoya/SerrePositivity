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

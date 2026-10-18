import SerrePositivity.KST.ProExcision
/-!
概要：K-L6 が所有する公開宣言の型と公理を監査する。
方針：各宣言を #check @ と #print axioms で確認する。
規約：標準三公理 propext・Classical.choice・Quot.sound のみを許す。
使われ方：KST §4・App. A の各保存単位。未完了の工程を証明済みとはしない。
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

#check @SerrePositivity.KST.ProExcision.spectral_successor_proZero
#print axioms SerrePositivity.KST.ProExcision.spectral_successor_proZero

#check @SerrePositivity.KST.ProExcision.proZero_of_exact
#print axioms SerrePositivity.KST.ProExcision.proZero_of_exact

#check @SerrePositivity.KST.ProExcision.proIso_of_injective_exact_proZero
#print axioms SerrePositivity.KST.ProExcision.proIso_of_injective_exact_proZero

#check @SerrePositivity.KST.ProExcision.spectral_page_proZero
#print axioms SerrePositivity.KST.ProExcision.spectral_page_proZero

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

#check @SerrePositivity.KST.ProExcision.koszulFilteredSpectralObject
#print axioms SerrePositivity.KST.ProExcision.koszulFilteredSpectralObject

#check @SerrePositivity.KST.ProExcision.koszulFilteredSpectralSequence
#print axioms SerrePositivity.KST.ProExcision.koszulFilteredSpectralSequence

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

#check @SerrePositivity.KST.ProExcision.finiteFirstPageComputation
#print axioms SerrePositivity.KST.ProExcision.finiteFirstPageComputation

#check @SerrePositivity.KST.ProExcision.koszulFirstPageXIso
#print axioms SerrePositivity.KST.ProExcision.koszulFirstPageXIso

#check @SerrePositivity.KST.ProExcision.filteredHomologySpectralObject
#print axioms SerrePositivity.KST.ProExcision.filteredHomologySpectralObject

#check @SerrePositivity.KST.ProExcision.filtrationIntervalHomologyIso
#print axioms SerrePositivity.KST.ProExcision.filtrationIntervalHomologyIso

#check @SerrePositivity.KST.ProExcision.singleTensorShiftIso
#print axioms SerrePositivity.KST.ProExcision.singleTensorShiftIso

#check @SerrePositivity.KST.ProExcision.flatLeftTensorHomologyIso
#print axioms SerrePositivity.KST.ProExcision.flatLeftTensorHomologyIso

#check @SerrePositivity.KST.ProExcision.singleTensorHomologyIso
#print axioms SerrePositivity.KST.ProExcision.singleTensorHomologyIso

#check @SerrePositivity.KST.ProExcision.koszulFirstPageConeIso
#print axioms SerrePositivity.KST.ProExcision.koszulFirstPageConeIso

#check @SerrePositivity.KST.ProExcision.truncationTensorConeIsoOfEq
#print axioms SerrePositivity.KST.ProExcision.truncationTensorConeIsoOfEq

#check @SerrePositivity.KST.ProExcision.koszulFirstPageSingleIso
#print axioms SerrePositivity.KST.ProExcision.koszulFirstPageSingleIso

#check @SerrePositivity.KST.ProExcision.koszulFirstPageTermIso
#print axioms SerrePositivity.KST.ProExcision.koszulFirstPageTermIso

#check @SerrePositivity.KST.ProExcision.koszulFirstPageHomologicalTermIso
#print axioms SerrePositivity.KST.ProExcision.koszulFirstPageHomologicalTermIso

#check @SerrePositivity.KST.ProExcision.kst_reindex_differential_degree
#print axioms SerrePositivity.KST.ProExcision.kst_reindex_differential_degree

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

#check @SerrePositivity.KST.ProExcision.tensorSplitBoundary_homogeneous_assoc
#print axioms SerrePositivity.KST.ProExcision.tensorSplitBoundary_homogeneous_assoc

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

#check @SerrePositivity.KST.ProExcision.filtrationTriangulated_delta
#print axioms SerrePositivity.KST.ProExcision.filtrationTriangulated_delta

#check @SerrePositivity.KST.ProExcision.filtrationInterval_delta
#print axioms SerrePositivity.KST.ProExcision.filtrationInterval_delta

#check @SerrePositivity.KST.ProExcision.filtrationInterval_delta_quotient
#print axioms SerrePositivity.KST.ProExcision.filtrationInterval_delta_quotient

#check @SerrePositivity.KST.ProExcision.filtrationInterval_delta_split
#print axioms SerrePositivity.KST.ProExcision.filtrationInterval_delta_split


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

#check @SerrePositivity.KST.ProExcision.tensorFiltration_delta_split
#print axioms SerrePositivity.KST.ProExcision.tensorFiltration_delta_split

#check @SerrePositivity.KST.ProExcision.tensorFiltrationIntervalHomologyIso
#print axioms SerrePositivity.KST.ProExcision.tensorFiltrationIntervalHomologyIso

#check @SerrePositivity.KST.ProExcision.tensorFiltration_delta_quotientIso
#print axioms SerrePositivity.KST.ProExcision.tensorFiltration_delta_quotientIso

#check @SerrePositivity.KST.ProExcision.tensorFiltrationBoundary
#print axioms SerrePositivity.KST.ProExcision.tensorFiltrationBoundary

#check @SerrePositivity.KST.ProExcision.koszulFirstPageQuotientIso
#print axioms SerrePositivity.KST.ProExcision.koszulFirstPageQuotientIso

#check @SerrePositivity.KST.ProExcision.koszulFirstPage_d_quotient
#print axioms SerrePositivity.KST.ProExcision.koszulFirstPage_d_quotient

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

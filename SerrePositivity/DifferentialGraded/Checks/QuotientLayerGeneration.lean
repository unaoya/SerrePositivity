module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLayerGeneration

/-! # 長さ層と有限長比較 cone の生成性の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms moduleCoproduct_finiteCellFactorTarget
#print axioms moduleSequentialColimit_finiteCellFactorTarget
#print axioms lengthLayerModule_finiteCellFactorTarget
#print axioms lengthLayerCone_finiteCellFactorTarget
#print axioms lengthModuleTransition_trW
#print axioms lengthZeroToStage_trW
#print axioms lengthZeroToStageCone_finiteCellFactorTarget

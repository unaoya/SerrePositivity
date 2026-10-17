module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLayerModule

/-! # 長さ層の加群射の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms lengthLayerProjection_prepend
#print axioms lengthLayerModuleComponent_action
#print axioms lengthLayerModuleComponent_naturality
#print axioms lengthLayerModuleProjection
#print axioms lengthModuleTransition_layerProjection
#print axioms lengthLayerModule_isColimit
#print axioms lengthModuleGradedIso
#print axioms lengthModuleGradedIso_π
#print axioms lengthModuleGradedFreeIso

module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHom

/-! # 実際の係数変更加群Hom比較の公理監査 -/
public section
open SerrePositivity.DifferentialGraded

#print axioms scalarTensorIso_inv_naturality
#print axioms scalarModuleParamNaturality
#print axioms scalarModuleParamTrans
#print axioms scalarModuleHom
#print axioms scalarModuleHom_π

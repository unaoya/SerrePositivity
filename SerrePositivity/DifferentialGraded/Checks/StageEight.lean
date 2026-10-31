module
public import SerrePositivity.DifferentialGraded

/-! # U0–U11統合入口の公開APIと再公理監査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example : leftUnitFunctor A B C ≅ 𝟭 (BimoduleCategory A B C) := leftUnitNatIso A B C
example : rightUnitFunctor A B C ≅ 𝟭 (BimoduleCategory A B C) := rightUnitNatIso A B C
example : leftTripleFunctor A B C E F ≅ rightTripleFunctor A B C E F :=
  associatorNatIso A B C E F

#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.enrichedTensorHomIso
#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.enrichedTensorHomEquiv_closedMap
#print axioms
      SerrePositivity.DifferentialGraded.BalancedTensor.enrichedTensorHomEquiv_naturality_param
#print axioms
      SerrePositivity.DifferentialGraded.BalancedTensor.enrichedTensorHomIso_source_naturality
#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.enrichedTensorHomIso_left_naturality
#print axioms
      SerrePositivity.DifferentialGraded.BalancedTensor.enrichedTensorHomIso_target_naturality
#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.leftTensorFunctor_preservesColimits
#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.rightTensorFunctor_preservesColimits
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftUnitNatIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitNatIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorNatIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_firstParam
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_middleParam
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_lastParam
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.triangle
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.pentagon

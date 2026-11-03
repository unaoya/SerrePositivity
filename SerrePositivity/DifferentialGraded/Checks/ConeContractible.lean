module
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-! # 恒等射のconeの全dg自然な収縮の受入検査 -/
@[expose] public section
universe u v
open CategoryTheory Limits SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : HasZeroObject (ModuleHomotopyCategory A D) := inferInstance

example (M : ModuleCategory A D) :
    IsZero ((moduleToHomotopy A D).obj (moduleCone A D (𝟙 M))) := moduleConeId_isZero A D M

#print axioms moduleHomCycle_zero
#print axioms moduleConeInlHomotopy
#print axioms moduleConeIdContractingElement
#print axioms moduleConeIdContractingElement_π
#print axioms moduleConeIdContractingElement_d
#print axioms moduleConeIdHomotopy
#print axioms moduleConeId_isZero
#print axioms moduleHomotopyHasZeroObject

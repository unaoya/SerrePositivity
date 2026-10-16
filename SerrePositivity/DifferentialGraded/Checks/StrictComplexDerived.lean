module
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexDerivedLinear
public import Mathlib.Data.ZMod.Basic

/-! # 既存有限射影ホモトピー圏から主導来圏への線形完全忠実関手の監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : (strictPerfectDGComplexToDerived A).Full := inferInstance
example : (strictPerfectDGComplexToDerived A).Faithful := inferInstance
example : (strictPerfectDGComplexToDerived A).Linear A := inferInstance
example : (perfectHomotopyToDGDerived A).Full := inferInstance
example : (perfectHomotopyToDGDerived A).Faithful := inferInstance
example : (perfectHomotopyToDGDerived A).Linear A := inferInstance
example : (perfectHomotopyToDGDerived A).Additive := inferInstance
example : (perfectHomotopyToDGDerived (ZMod 2)).Full := inferInstance
example : (perfectHomotopyToDGDerived (ZMod 2)).Linear (ZMod 2) := inferInstance

#print axioms strictPerfectDGComplexToRingModule
#print axioms strictPerfectDGComplexToRingModuleHomotopyFull
#print axioms strictPerfectDGComplexToRingModuleHomotopyFaithful
#print axioms strictPerfectDGComplexToDerived
#print axioms strictPerfectDGComplexToDerivedFull
#print axioms strictPerfectDGComplexToDerivedFaithful
#print axioms strictPerfectDGComplexToDerivedAdditive
#print axioms strictPerfectDGComplexToDerivedLinear
#print axioms perfectHomotopyToDGDerived
#print axioms perfectHomotopyToDGDerivedFull
#print axioms perfectHomotopyToDGDerivedFaithful
#print axioms perfectHomotopyToDGDerivedAdditive
#print axioms perfectHomotopyToDGDerivedLinear
#print axioms strictPerfectDGComplexToPerfectCompDerived

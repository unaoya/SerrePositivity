module
public import SerrePositivity.DifferentialGraded.Perfect.RingPerfectComparison
public import Mathlib.Data.ZMod.Basic

/-! # 既存PerfectHomotopyと主Perfとの線形完全忠実比較の監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : (strictPerfectDGComplexToDGPerfect A).Full := inferInstance
example : (strictPerfectDGComplexToDGPerfect A).Faithful := inferInstance
example : (strictPerfectDGComplexToDGPerfect A).Linear A := inferInstance
example : (perfectHomotopyToDGPerfect A).Full := inferInstance
example : (perfectHomotopyToDGPerfect A).Faithful := inferInstance
example : (perfectHomotopyToDGPerfect A).Linear A := inferInstance
example : (perfectHomotopyToDGPerfect A).Additive := inferInstance
example : perfectHomotopyToDGPerfect A ⋙ perfectModuleInclusion A PUnit.{1} Set.univ ≅
    perfectHomotopyToDGDerived A := perfectHomotopyToDGPerfectCompInclusion A
example : (perfectHomotopyToDGPerfect (ZMod 2)).Full := inferInstance

#print axioms strictPerfectDGComplexToDGPerfect
#print axioms strictPerfectDGComplexToDGPerfectFull
#print axioms strictPerfectDGComplexToDGPerfectFaithful
#print axioms strictPerfectDGComplexToDGPerfectAdditive
#print axioms strictPerfectDGComplexToDGPerfectLinear
#print axioms strictPerfectDGComplexToPerfectDGCompDerived
#print axioms strictPerfectDGComplexToDGPerfectCompInclusion
#print axioms perfectHomotopyToDGPerfect
#print axioms perfectHomotopyToDGPerfectFull
#print axioms perfectHomotopyToDGPerfectFaithful
#print axioms perfectHomotopyToDGPerfectAdditive
#print axioms perfectHomotopyToDGPerfectLinear
#print axioms perfectHomotopyToDGPerfectCompInclusion

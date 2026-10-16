module
public import SerrePositivity.DifferentialGraded.Perfect.RingPerfectTriangulated
public import Mathlib.Data.ZMod.Basic

/-! # 既存PerfectHomotopyから主Perfへの実際の比較の三角整合性 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Pretriangulated
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : (perfectHomotopyToDGDerived A).CommShift ℤ := inferInstance
example : (perfectHomotopyToDGDerived A).IsTriangulated := inferInstance
example : (perfectHomotopyToDGPerfect A).CommShift ℤ := inferInstance
example : (perfectHomotopyToDGPerfect A).IsTriangulated := inferInstance
example : NatTrans.CommShift (perfectHomotopyToDGPerfectCompInclusion A).hom ℤ := inferInstance
example (T : Triangle (SerrePositivity.PerfectHomotopy A))
    (hT : T ∈ distTriang (SerrePositivity.PerfectHomotopy A)) :
    (perfectHomotopyToDGPerfect A).mapTriangle.obj T ∈
      distTriang (PerfectModuleCategory A PUnit.{1}) :=
  (perfectHomotopyToDGPerfect A).map_distinguished T hT
example : (perfectHomotopyToDGPerfect (ZMod 2)).IsTriangulated := inferInstance
example : (perfectHomotopyToDGPerfect (ZMod 2)).CommShift ℤ := inferInstance

#print axioms complexClosedRingModuleIso
#print axioms complexHomotopyRingDerivedIso
#print axioms strictPerfectDGComplexDerivedCanonicalIso
#print axioms perfectHomotopyToDGDerivedCanonicalIso
#print axioms perfectHomotopyToDGDerivedCommShift
#print axioms perfectHomotopyToDGDerivedCanonicalIsoCommShift
#print axioms perfectHomotopyToDGDerivedIsTriangulated
#print axioms perfectHomotopyToDGPerfectCommShift
#print axioms perfectHomotopyToDGPerfectCompInclusionCommShift
#print axioms perfectHomotopyToDGPerfectIsTriangulated

module
public import SerrePositivity.DifferentialGraded.Perfect.RingRetract
public import Mathlib.Data.ZMod.Basic

/-! # 一対象Aのperfect比較とretractの受入監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Idempotents
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example (X : PerfectModuleCategory A PUnit.{1}) :
    ∃ P : SerrePositivity.PerfectHomotopy A,
      Nonempty (Retract X ((perfectHomotopyToDGPerfect A).obj P)) :=
  perfectModule_ring_retract_of_perfectHomotopy A X
example (X : PerfectModuleCategory (ZMod 2) PUnit.{1}) :
    ∃ P : SerrePositivity.PerfectHomotopy (ZMod 2),
      Nonempty (Retract X ((perfectHomotopyToDGPerfect (ZMod 2)).obj P)) :=
  perfectModule_ring_retract_of_perfectHomotopy (ZMod 2) X

#print axioms ringFiniteCellPerfectHomotopy
#print axioms ringFiniteCellPerfectHomotopyDerivedIso
#print axioms perfectModule_ring_retract_of_perfectHomotopy

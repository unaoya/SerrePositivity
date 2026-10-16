module
public import SerrePositivity.DifferentialGraded.Perfect.RingEnhancement
public import Mathlib.Data.ZMod.Basic

/-! # 有界有限射影複体の主Perfへのdg比較の受入検査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example (P : Complex A) (hP : SerrePositivity.strictlyPerfectComplex A P) :
    modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P)) :=
  strictlyPerfectComplex_ringDerived_perfect A P hP
example (P : StrictPerfectDGComplex A) : PerfectDGModule A PUnit.{1} :=
  (strictPerfectDGComplexToPerfectDG A).obj P
example (P N : StrictPerfectDGComplex A) :
    IsIso ((strictPerfectDGComplexToPerfectDG A).map P N) := by
  change IsIso (ringConstantHomIso A P.val N.val).inv
  infer_instance
example : (strictPerfectDGComplexToPerfectDG A).onHomotopy.Full := inferInstance
example : (strictPerfectDGComplexToPerfectDG A).onHomotopy.Faithful := inferInstance
example : (strictPerfectDGComplexToPerfectDG A).onHomotopy.Linear A := inferInstance
example (P : StrictPerfectDGComplex (ZMod 2)) :
    PerfectDGModule (ZMod 2) PUnit.{1} := (strictPerfectDGComplexToPerfectDG (ZMod 2)).obj P
example : (strictPerfectDGComplexToPerfectDG (ZMod 2)).onHomotopy.Full := inferInstance

#print axioms complexToRingModuleEvaluationIso
#print axioms complexToRingModuleDerivedEvaluationIso
#print axioms ringComplexDerivedUnitIso
#print axioms ringComplexDerived_perfect_of_shortExact
#print axioms ringComplexDerived_perfect_of_finite_range
#print axioms strictlyPerfectComplex_ringDerived_perfect
#print axioms strictlyPerfectComplex_ringModule_perfectProjective
#print axioms strictPerfectDGComplexToPerfectDG
#print axioms strictPerfectDGComplexToPerfectDG_comp_inclusion
#print axioms strictPerfectDGComplexToPerfectDGHomotopyFull
#print axioms strictPerfectDGComplexToPerfectDGHomotopyFaithful

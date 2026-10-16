module
public import SerrePositivity.DifferentialGraded.Perfect.RingFiniteCellImage
public import Mathlib.Data.ZMod.Basic

/-! # 一対象Aの有限cellと既存有限射影複体の比較の監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example (P : Complex A) (hP : CategoryTheory.Limits.IsZero P) :
    SerrePositivity.strictlyPerfectComplex A P := strictlyPerfectComplex_of_isZero A P hP
example (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M] (n : ℤ) :
    SerrePositivity.strictlyPerfectComplex A
      ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) n).obj M) :=
  strictlyPerfectComplex_single A M n
example (S : Set PUnit.{1}) (M : ModuleCategory A PUnit.{1})
    (hM : moduleFiniteCellOver A PUnit.{1} S M) :
    SerrePositivity.strictlyPerfectComplex A
      ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M) :=
  moduleFiniteCell_ringEvaluation_strictlyPerfect A hM
example (M : ModuleCategory (ZMod 2) PUnit.{1})
    (hM : moduleFiniteCell (ZMod 2) PUnit.{1} M) :
    SerrePositivity.strictlyPerfectComplex (ZMod 2)
      ((moduleEvaluation (ZMod 2) PUnit.{1} PUnit.unit).obj M) :=
  moduleFiniteCell_ringEvaluation_strictlyPerfect (ZMod 2) hM

#print axioms strictlyPerfectComplex_of_iso
#print axioms strictlyPerfectComplex_of_isZero
#print axioms strictlyPerfectComplex_single
#print axioms moduleFiniteCell_ringEvaluation_strictlyPerfect
#print axioms strictPerfectDGComplexToPerfectDG_essImage_of_finiteCell

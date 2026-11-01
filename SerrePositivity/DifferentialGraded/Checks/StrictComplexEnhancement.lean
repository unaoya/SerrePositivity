module
public import SerrePositivity.DifferentialGraded.Perfect.Ring.FiniteProjectiveComparison
public import Mathlib.Data.ZMod.Basic

/-! # 既存有限射影複体の全Hom dg表示とH⁰線形同値 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : DGCategory A (StrictPerfectDGComplex A) := inferInstance
example (M N : StrictPerfectDGComplex A) :
    homObject A (StrictPerfectDGComplex A) M N = homComplex A M.val N.val := rfl
example (M N : StrictPerfectDGComplex A) (n : ℤ) :
    (homObject A (StrictPerfectDGComplex A) M N).d n (n + 1) =
      (homComplex A M.val N.val).d n (n + 1) := rfl
example : (strictPerfectDGComplexToPerfect A).IsEquivalence := inferInstance
example : (strictPerfectDGComplexToPerfect A).Linear A := inferInstance
example : (strictPerfectDGComplexHomotopyEquivalence A).inverse.Linear A := inferInstance
example : (strictPerfectDGComplexHomotopyEquivalence A).inverse.Additive := inferInstance
example (P : Complex A) (hP : SerrePositivity.strictlyPerfectComplex A P) :
    StrictPerfectDGComplex A := ⟨P, hP⟩
example : (strictPerfectDGComplexToPerfect (ZMod 2)).IsEquivalence := inferInstance

#print axioms strictPerfectDGComplexInclusion
#print axioms strictPerfectDGComplexInclusionHomotopyFull
#print axioms strictPerfectDGComplexInclusionHomotopyFaithful
#print axioms strictPerfectDGComplexToHomotopy
#print axioms strictPerfectDGComplexToHomotopy_obj_perfect
#print axioms strictPerfectDGComplexToPerfect
#print axioms strictPerfectDGComplexToPerfectFull
#print axioms strictPerfectDGComplexToPerfectFaithful
#print axioms strictPerfectDGComplexToPerfectEssSurj
#print axioms strictPerfectDGComplexToPerfectIsEquivalence
#print axioms strictPerfectDGComplexHomotopyEquivalence
#print axioms strictPerfectDGComplexToHomotopyAdditive
#print axioms strictPerfectDGComplexToHomotopyLinear
#print axioms strictPerfectDGComplexToPerfectAdditive
#print axioms strictPerfectDGComplexToPerfectLinear
#print axioms strictPerfectDGComplexHomotopyEquivalenceFunctorAdditive
#print axioms strictPerfectDGComplexHomotopyEquivalenceFunctorLinear
#print axioms strictPerfectDGComplexToPerfectCompInclusion

module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 実際のdg shift・H⁰ shiftのcoherence・Perf比較の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : HasShift (PerfectDGHomotopyCategoryOver A D S) ℤ := inferInstance
example (S : Set D) (s : ℤ) :
    shiftFunctor (PerfectDGHomotopyCategoryOver A D S) s =
      (perfectDGModuleShiftDG A D S s).onHomotopy :=
  perfectDGHomotopy_shiftFunctor A D S s
example (S : Set D) : (perfectDGModuleToPerfect A D S).CommShift ℤ := inferInstance
example (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).inverse.CommShift ℤ := inferInstance
example (S : Set D) : (perfectDGModuleHomotopyEquivalence A D S).CommShift ℤ := inferInstance
example (S : Set D) (X : PerfectDGHomotopyCategoryOver A D S) :
    Nonempty ((X⟦(2 : ℤ)⟧)⟦(-3 : ℤ)⟧ ≅ X⟦(-1 : ℤ)⟧) :=
  ⟨((shiftFunctorAdd' _ (2 : ℤ) (-3) (-1) (by norm_num)).app X).symm⟩
example : (perfectDGModuleToPerfect (ZMod 2) PUnit.{1} ∅).CommShift ℤ := inferInstance

#print axioms moduleShiftDGHomotopyIso
#print axioms perfectDGModuleShiftHomotopyInclusionIso
#print axioms perfectDGModuleShiftHomotopyDerivedIso
#print axioms perfectDGModuleShiftHomotopyPerfectIso
#print axioms perfectDGModuleInverseShiftIso
#print axioms perfectDGHomotopyHasShift
#print axioms perfectDGHomotopy_shiftFunctor
#print axioms perfectDGHomotopyShiftAdditive
#print axioms perfectDGModuleHomotopyEquivalenceInverseCommShift
#print axioms perfectDGModuleHomotopyEquivalenceFunctorCommShift
#print axioms perfectDGModuleHomotopyEquivalenceCommShift
#print axioms perfectDGModuleToPerfectCommShift

#print axioms perfectDGModuleToPerfect_commShiftIso

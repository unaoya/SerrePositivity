module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 小さいdg代表系のshift・三角構造と実際の包含の比較 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : Small.{u} (SmallPerfectDGModuleOver A D S) := inferInstance
example (S : Set D) : HasShift (SmallPerfectDGHomotopyCategoryOver A D S) ℤ := inferInstance
example (S : Set D) : IsTriangulated (SmallPerfectDGHomotopyCategoryOver A D S) := inferInstance
example (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).inverse.IsTriangulated := inferInstance
example (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).CommShift ℤ := inferInstance
example (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.CommShift ℤ := inferInstance
example (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.IsTriangulated := inferInstance
example (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.IsEquivalence := inferInstance
example (S : Set D) (X : SmallPerfectDGHomotopyCategoryOver A D S) :
    Nonempty ((X⟦(-3 : ℤ)⟧)⟦(2 : ℤ)⟧ ≅ X⟦(-1 : ℤ)⟧) :=
  ⟨((shiftFunctorAdd' _ (-3 : ℤ) 2 (-1) (by norm_num)).app X).symm⟩
example : IsTriangulated (SmallPerfectDGHomotopyCategoryOver (ZMod 2) PUnit.{1} ∅) := inferInstance

#print axioms smallPerfectDGShiftHomotopyFunctor
#print axioms smallPerfectDGShiftHomotopyIso
#print axioms smallPerfectDGHomotopyHasShift
#print axioms smallPerfectDGHomotopy_shiftFunctor
#print axioms smallPerfectDGHomotopyShiftAdditive
#print axioms smallPerfectDGModuleHomotopyEquivalenceFunctorCommShift
#print axioms smallPerfectDGModuleHomotopyEquivalenceInverseCommShift
#print axioms smallPerfectDGModuleHomotopyEquivalenceCommShift
#print axioms smallPerfectDGModuleToPerfectCommShift
#print axioms smallPerfectDGHomotopyHasZeroObject
#print axioms smallPerfectDGHomotopyPretriangulated
#print axioms smallPerfectDGModuleToPerfectIsTriangulated
#print axioms smallPerfectDGHomotopyIsTriangulated
#print axioms smallPerfectDGModuleHomotopyEquivalenceIsTriangulated
#print axioms smallPerfectDGModuleInclusionPerfectIso
#print axioms smallPerfectDGModuleInclusionHomotopyCommShift
#print axioms smallPerfectDGModuleInclusionPerfectIsoCommShift
#print axioms smallPerfectDGModuleInclusionHomotopyIsTriangulated
#print axioms smallPerfectDGModuleInclusionHomotopyIsEquivalence

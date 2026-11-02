module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # perfect dg H⁰の三角構造と主Perf三角同値の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits Pretriangulated
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : HasZeroObject (PerfectDGHomotopyCategoryOver A D S) := inferInstance
example (S : Set D) : Pretriangulated (PerfectDGHomotopyCategoryOver A D S) := inferInstance
example (S : Set D) : IsTriangulated (PerfectDGHomotopyCategoryOver A D S) := inferInstance
example (S : Set D) : (perfectDGModuleToPerfect A D S).IsTriangulated := inferInstance
example (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).inverse.IsTriangulated := inferInstance
example (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).IsTriangulated := inferInstance
example (S : Set D) (T : Triangle (PerfectDGHomotopyCategoryOver A D S)) :
    (perfectDGModuleToPerfect A D S).mapTriangle.obj T ∈
      distTriang (PerfectModuleCategoryOver A D S) ↔
    T ∈ distTriang (PerfectDGHomotopyCategoryOver A D S) :=
  (perfectDGModuleToPerfect A D S).map_distinguished_iff T
example (S : Set D) (X : PerfectDGHomotopyCategoryOver A D S) :
    contractibleTriangle X ∈ distTriang (PerfectDGHomotopyCategoryOver A D S) :=
  contractible_distinguished X
example : IsTriangulated (PerfectDGHomotopyCategoryOver (ZMod 2) PUnit.{1} ∅) := inferInstance

#print axioms dgComparisonHasZeroObject
#print axioms dgComparisonPretriangulated
#print axioms perfectDGHomotopyHasZeroObject
#print axioms perfectDGHomotopyPretriangulated
#print axioms perfectDGHomotopy_distinguished_iff
#print axioms perfectDGModuleToPerfectIsTriangulated
#print axioms perfectDGHomotopyIsTriangulated
#print axioms perfectDGModuleHomotopyEquivalenceIsTriangulated

module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 実際のdg shiftに対する主導来三角比較の計算 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : (perfectDGModuleToDerived A D S).CommShift ℤ := inferInstance
example (S : Set D) : (perfectDGModuleToDerived A D S).IsTriangulated := inferInstance
example (S : Set D) :
    NatTrans.CommShift (perfectDGModuleToPerfectCompInclusion A D S).hom ℤ := inferInstance
example (S : Set D) (s : ℤ) (X : PerfectDGHomotopyCategoryOver A D S) :
    ((perfectDGModuleToDerived A D S).commShiftIso s).hom.app X =
      (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X :=
  perfectDGModuleToDerived_commShiftIso_hom_app A D S s X
example : (perfectDGModuleToDerived (ZMod 2) PUnit.{1} ∅).IsTriangulated := inferInstance

#print axioms perfectDGModuleShiftHomotopyPerfectIso_hom_inclusion
#print axioms perfectDGModuleToDerivedCommShift
#print axioms perfectDGModuleToPerfectCompInclusionCommShift
#print axioms perfectDGModuleToDerivedIsTriangulated
#print axioms perfectDGModuleToDerived_commShiftIso_hom_app

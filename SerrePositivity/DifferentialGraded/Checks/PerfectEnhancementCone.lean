module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 実際の射影的perfect dg cone三角形と包含の射計算 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Pretriangulated
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : (perfectDGModuleInclusion A D S).onClosed.Full := inferInstance
example (S : Set D) : (perfectDGModuleInclusion A D S).onClosed.Faithful := inferInstance
example (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleConeTriangle A D S M N f).obj₃ =
      perfectDGModuleHomotopyObj A D S (perfectDGModuleCone A D S M N f) := rfl
example (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleConeTriangle A D S M N f).mor₁ ≫
      (perfectDGModuleConeTriangle A D S M N f).mor₂ = 0 :=
  perfectDGModuleConeTriangle_comp_zero₁₂ A D S M N f
example (S : Set D) (M : PerfectDGModuleOver A D S) :
    (perfectDGModuleHomotopyObj A D S M)⟦(-3 : ℤ)⟧ =
      perfectDGModuleHomotopyObj A D S (perfectDGModuleShiftObj A D S (-3) M) :=
  perfectDGModuleHomotopyObj_shift A D S M (-3)
example : Triangle (PerfectDGHomotopyCategoryOver (ZMod 2) PUnit.{1} ∅) :=
  perfectDGModuleConeTriangle (ZMod 2) PUnit.{1} ∅
    (perfectDGModuleZero (ZMod 2) PUnit.{1} ∅) (perfectDGModuleZero (ZMod 2) PUnit.{1} ∅) 0

#print axioms perfectDGModuleInclusionClosedFull
#print axioms perfectDGModuleInclusionClosedFaithful
#print axioms perfectDGModuleHomotopyObj
#print axioms perfectDGModuleHomotopyMap
#print axioms perfectDGModuleHomotopyMap_inclusion
#print axioms perfectDGModuleHomotopyObj_shift
#print axioms perfectDGModuleConeTriangle
#print axioms perfectDGModuleConeTriangle_mor₁
#print axioms perfectDGModuleConeTriangle_mor₂
#print axioms perfectDGModuleHomotopyMap_comp
#print axioms perfectDGModuleHomotopyMap_id
#print axioms perfectDGModuleHomotopyMap_zero
#print axioms perfectDGModuleConeTriangle_comp_zero₁₂

#print axioms perfectDGModuleHomotopyMap_toDerived

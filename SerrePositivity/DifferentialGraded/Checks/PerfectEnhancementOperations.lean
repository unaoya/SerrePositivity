module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 射影的perfect加群の実際の有限操作と主局所化比較 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (M : PerfectDGModuleOver A D S) (s : ℤ) :
    (perfectDGModuleShiftObj A D S s M).val = shiftModule s M.val := rfl
example (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleCone A D S M N f).val =
      ForgetEnrichment.to (Complex A) (moduleCone A D f) := rfl
example (S : Set D) (s : ℤ) :
    DGFunctor.comp (perfectDGModuleShiftDG A D S s) (perfectDGModuleInclusion A D S) =
      DGFunctor.comp (perfectDGModuleInclusion A D S) (moduleShiftDG A D s) :=
  perfectDGModuleShiftDG_comp_inclusion A D S s
example : PerfectDGModuleOver (ZMod 2) PUnit.{1} ∅ :=
  perfectDGModuleShiftObj (ZMod 2) PUnit.{1} ∅ (-3)
    (perfectDGModuleZero (ZMod 2) PUnit.{1} ∅)
example (S : Set D) (M : PerfectDGModuleOver A D S) :
    Nonempty ((perfectDGModuleToDerived A D S).obj
      ((toHomotopy A (PerfectDGModuleOver A D S)).obj
        (ForgetEnrichment.of (Complex A) (perfectDGModuleShiftObj A D S 2 M))) ≅
    ((perfectDGModuleToDerived A D S).obj
      ((toHomotopy A (PerfectDGModuleOver A D S)).obj
        (ForgetEnrichment.of (Complex A) M)))⟦(2 : ℤ)⟧) :=
  ⟨perfectDGModuleShiftDerivedIso A D S 2 M⟩

#print axioms modulePerfectProjectiveOver_zero
#print axioms modulePerfectProjectiveOver_shift
#print axioms modulePerfectProjectiveOver_cone
#print axioms modulePerfectProjectiveOver_biprod
#print axioms perfectDGModuleZero
#print axioms perfectDGModuleShiftObj
#print axioms perfectDGModuleShiftDG
#print axioms perfectDGModuleShiftDG_comp_inclusion
#print axioms perfectDGModuleBiprod
#print axioms perfectDGModuleCone
#print axioms perfectDGModuleClosedToDerivedIso
#print axioms perfectDGModuleShiftDerivedIso
#print axioms DGFunctor.restrict
#print axioms DGFunctor.restrict_comp_inclusion

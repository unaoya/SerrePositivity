module
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 指定導来圏内のPerf・retract・有限生成元・shift検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits
open scoped ZeroObject
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : HasZeroObject (PerfectModuleCategoryOver A D S) := inferInstance

example (S : Set D) : (perfectModuleInclusion A D S).Faithful := by
  dsimp [perfectModuleInclusion]
  infer_instance

example (S : Set D) : HasShift (PerfectModuleCategoryOver A D S) ℤ := inferInstance
example (S : Set D) : (perfectModuleInclusion A D S).CommShift ℤ := inferInstance

example {S : Set D} {X : DerivedModuleCategory A D} (hX : modulePerfectOver A D S X) :
    ∃ M : ModuleCategory A D, moduleFiniteCellOver A D S M ∧
      Nonempty (Retract X ((moduleToDerived A D).obj M)) :=
  (modulePerfectOver_iff A D S X).1 hX

example {S : Set D} {X : DerivedModuleCategory A D} (hX : modulePerfectOver A D S X) :
    ∃ t : Finset D, (↑t : Set D) ⊆ S ∧ modulePerfectOver A D (↑t : Set D) X :=
  (modulePerfectOver_iff_finite_generators A D S X).1 hX

example {X Y : DerivedModuleCategory A D} (r : Retract X Y)
    (hY : modulePerfect A D Y) : modulePerfect A D X :=
  (modulePerfect A D).prop_of_retract r hY

example (S : Set D) : modulePerfectOver A D S 0 := modulePerfectOver_zero A D S

example (x : PUnit.{1}) : modulePerfect (ZMod 2) PUnit.{1}
    ((moduleToDerived (ZMod 2) PUnit.{1}).obj
      (ForgetEnrichment.of (Complex (ZMod 2)) (representable (ZMod 2) x))) :=
  modulePerfectOver_representable (ZMod 2) PUnit.{1} x (Set.mem_univ x)

#print axioms derivedFiniteCellOver
#print axioms modulePerfectOver
#print axioms modulePerfect
#print axioms PerfectModuleCategoryOver
#print axioms PerfectModuleCategory
#print axioms perfectModuleInclusion
#print axioms modulePerfectOverStableUnderRetracts
#print axioms modulePerfectOverClosedUnderIso
#print axioms modulePerfectOver_iff
#print axioms modulePerfectOver_of_finiteCell
#print axioms modulePerfectOver_representable
#print axioms modulePerfectOver_mono
#print axioms modulePerfectOver_of_retract
#print axioms modulePerfectOver_of_iso
#print axioms modulePerfectOver_iff_finite_generators
#print axioms modulePerfect_iff
#print axioms modulePerfect_iff_finite_generators
#print axioms modulePerfectOverNonempty
#print axioms modulePerfectOverContainsZero
#print axioms modulePerfectOver_zero
#print axioms modulePerfectStableUnderRetracts
#print axioms modulePerfectOver_le_iff
#print axioms moduleFiniteCellOverStableUnderShift
#print axioms derivedFiniteCellOverStableUnderShift
#print axioms modulePerfectOverStableUnderShift
#print axioms modulePerfectOver_shift
#print axioms modulePerfect_shift
#print axioms perfectModuleInclusionCommShift
#print axioms modulePerfectStableUnderShift

module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 小さいfinite cell代表系とPerfの本質的小性の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : Small.{u} (ModuleFiniteCellStageIndex A D S) :=
  inferInstance
example (S : Set D) : ObjectProperty.EssentiallySmall.{u} (moduleFiniteCellOver A D S) :=
  inferInstance
example (S : Set D) : ObjectProperty.EssentiallySmall.{u} (modulePerfectOver A D S) :=
  inferInstance
example (S : Set D) : EssentiallySmall.{u} (PerfectModuleCategoryOver A D S) :=
  inferInstance
example (S : Set D) (M : ModuleCategory A D) (h : moduleFiniteCellOver A D S M) :
    ∃ i : ModuleFiniteCellStageIndex A D S,
      Nonempty (moduleFiniteCellStageObject A D S i ≅ M) :=
  moduleFiniteCellOver_exists_stage A D h
example : EssentiallySmall.{0} (PerfectModuleCategoryOver (ZMod 2) PUnit.{1} Set.univ) :=
  inferInstance
example : EssentiallySmall.{0} (PerfectModuleCategoryOver (ZMod 2) PUnit.{1} ∅) :=
  inferInstance
example (S : Set D) : SmallCategory (SmallModel.{u} (PerfectModuleCategoryOver A D S)) :=
  inferInstance

#print axioms ModuleFiniteCellFamily
#print axioms moduleFiniteCellFamilyZero
#print axioms moduleFiniteCellFamilyNext
#print axioms moduleFiniteCellStage
#print axioms moduleFiniteCellStage_succ
#print axioms moduleFiniteCellStage_lift
#print axioms moduleFiniteCellStageObject
#print axioms moduleFiniteCellStageObject_finite
#print axioms moduleConeIsoOfArrowIso
#print axioms moduleFiniteCellStage_pair
#print axioms ModuleFiniteCellCode.exists_stage
#print axioms moduleFiniteCellOver_exists_stage
#print axioms moduleFiniteCellOverEssentiallySmall
#print axioms derivedFiniteCellOverEssentiallySmall
#print axioms modulePerfectOverEssentiallySmall
#print axioms perfectModuleCategoryOverEssentiallySmall
#print axioms modulePerfectOver_exists_small_representatives

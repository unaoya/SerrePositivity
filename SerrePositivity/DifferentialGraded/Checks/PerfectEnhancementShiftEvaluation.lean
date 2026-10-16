module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementShiftEvaluation
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 閉零代表でのdg shift比較の計算と宇宙・符号の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M : ModuleCategory A D) :
    (moduleShiftDGHomotopyIso A D (-3)).hom.app ((moduleToHomotopy A D).obj M) =
      ((moduleToHomotopy A D).commShiftIso (-3 : ℤ)).hom.app M :=
  moduleShiftDGHomotopyIso_closed_hom_app A D (-3) M
example (S : Set D) (M : PerfectDGModuleOver A D S) :
    (perfectDGModuleShiftHomotopyDerivedIso A D S 2).hom.app
        (perfectDGModuleHomotopyObj A D S M) =
      ((moduleToHomotopy A D ⋙ moduleHomotopyToDerivedClosed A D).commShiftIso (2 : ℤ)).hom.app
        (ForgetEnrichment.of (Complex A) M.val) :=
  perfectDGModuleShiftHomotopyDerivedIso_hom_obj A D S 2 M
example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    (moduleShiftDGHomotopyIso (ZMod 2) PUnit.{1} 1).hom.app
        ((moduleToHomotopy (ZMod 2) PUnit.{1}).obj M) =
      ((moduleToHomotopy (ZMod 2) PUnit.{1}).commShiftIso (1 : ℤ)).hom.app M :=
  moduleShiftDGHomotopyIso_closed_hom_app (ZMod 2) PUnit.{1} 1 M

#print axioms quotientComparison_hom_app
#print axioms comparisonWhiskerLeft_hom_app
#print axioms comparisonCompose_hom_app
#print axioms moduleShiftDGHomotopyIso_closed_hom_app
#print axioms perfectDGModuleShiftHomotopyInclusionIso_hom_app
#print axioms perfectDGModuleShiftHomotopyInclusionIso_hom_obj
#print axioms perfectDGModuleShiftHomotopyDerivedIso_hom_obj

#print axioms restrictHomotopyComparisonIso
#print axioms restrictHomotopyComparison_hom_app

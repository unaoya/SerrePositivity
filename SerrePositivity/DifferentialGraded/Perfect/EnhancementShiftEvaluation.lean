module
public import SerrePositivity.DifferentialGraded.Category.RestrictionComparison
public import SerrePositivity.DifferentialGraded.Module.ShiftComparisonEvaluation
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementCone
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementDerivedComparison

/-! # 実際の閉零代表におけるperfect dg shift比較の計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 包含のshift比較は任意のH⁰対象で、全加群のshift比較の成分となる。 -/
lemma perfectDGModuleShiftHomotopyInclusionIso_hom_app (S : Set D) (s : ℤ)
    (X : PerfectDGHomotopyCategoryOver A D S) :
    (perfectDGModuleShiftHomotopyInclusionIso A D S s).hom.app X =
      (moduleShiftDGHomotopyIso A D s).hom.app
        ((perfectDGModuleInclusion A D S).onHomotopy.obj X) :=
  restrictHomotopyComparison_hom_app (moduleShiftDG A D s) (modulePerfectProjectiveOver A D S)
    (fun _ h => modulePerfectProjectiveOver_shift A D h s)
    (shiftFunctor (ModuleHomotopyCategory A D) s) (moduleShiftDGHomotopyIso A D s) X


/-- perfect dg shiftと包含の比較は、実際の加群代表で商関手のshift比較を返す。 -/
lemma perfectDGModuleShiftHomotopyInclusionIso_hom_obj (S : Set D) (s : ℤ)
    (M : PerfectDGModuleOver A D S) :
    (perfectDGModuleShiftHomotopyInclusionIso A D S s).hom.app
        (perfectDGModuleHomotopyObj A D S M) =
      ((moduleToHomotopy A D).commShiftIso s).hom.app (ForgetEnrichment.of (Complex A) M.val) :=
  (perfectDGModuleShiftHomotopyInclusionIso_hom_app A D S s _).trans
    (moduleShiftDGHomotopyIso_closed_hom_app A D s (ForgetEnrichment.of (Complex A) M.val))

/-- 主導来shift比較は閉零代表上で、既存のK(D)経由の合成関手のshift比較に一致する。 -/
lemma perfectDGModuleShiftHomotopyDerivedIso_hom_obj (S : Set D) (s : ℤ)
    (M : PerfectDGModuleOver A D S) :
    (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app
        (perfectDGModuleHomotopyObj A D S M) =
      ((moduleToHomotopy A D ⋙ moduleHomotopyToDerivedClosed A D).commShiftIso s).hom.app
        (ForgetEnrichment.of (Complex A) M.val) := by
  have h := comparisonCompose_hom_app
    (perfectDGModuleShiftDG A D S s).onHomotopy (perfectDGModuleInclusion A D S).onHomotopy
    (moduleHomotopyToDerivedClosed A D) (shiftFunctor (ModuleHomotopyCategory A D) s)
    (shiftFunctor (DerivedModuleCategory A D) s)
    (perfectDGModuleShiftHomotopyInclusionIso A D S s)
    ((moduleHomotopyToDerivedClosed A D).commShiftIso s) (perfectDGModuleHomotopyObj A D S M)
  let Y : ModuleCategory A D := ForgetEnrichment.of (Complex A) M.val
  have h' := congrArg (fun a => (moduleHomotopyToDerivedClosed A D).map a ≫
    ((moduleHomotopyToDerivedClosed A D).commShiftIso s).hom.app ((moduleToHomotopy A D).obj Y))
    (perfectDGModuleShiftHomotopyInclusionIso_hom_obj A D S s M)
  exact h.trans (h'.trans (Functor.commShiftIso_comp_hom_app
    (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D) s Y).symm)

end SerrePositivity.DifferentialGraded

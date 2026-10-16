module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementLinear
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopyComparison

/-! # 射影的perfect dg shiftのH⁰と主Perfにおける自然比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際のdg shiftのH⁰は、H⁰包含の後の既存K(D)のshiftと自然に可換である。 -/
def perfectDGModuleShiftHomotopyInclusionIso (S : Set D) (s : ℤ) :
    (perfectDGModuleShiftDG A D S s).onHomotopy ⋙ (perfectDGModuleInclusion A D S).onHomotopy ≅
      (perfectDGModuleInclusion A D S).onHomotopy ⋙ shiftFunctor (ModuleHomotopyCategory A D) s :=
  eqToIso ((DGFunctor.onHomotopy_comp _ _).symm.trans
    ((congrArg (fun F : DGFunctor A (PerfectDGModuleOver A D S) (RightModule A D) => F.onHomotopy)
      (perfectDGModuleShiftDG_comp_inclusion A D S s)).trans
        (DGFunctor.onHomotopy_comp _ _))) ≪≫
    Functor.isoWhiskerLeft (perfectDGModuleInclusion A D S).onHomotopy
      (moduleShiftDGHomotopyIso A D s)

/-- 実際のdg shiftのH⁰比較は全てのH⁰射について主導来shiftと自然に可換である。 -/
def perfectDGModuleShiftHomotopyDerivedIso (S : Set D) (s : ℤ) :
    (perfectDGModuleShiftDG A D S s).onHomotopy ⋙ perfectDGModuleToDerived A D S ≅
      perfectDGModuleToDerived A D S ⋙ shiftFunctor (DerivedModuleCategory A D) s :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleShiftHomotopyInclusionIso A D S s)
      (moduleHomotopyToDerivedClosed A D) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (perfectDGModuleInclusion A D S).onHomotopy
      ((moduleHomotopyToDerivedClosed A D).commShiftIso s) ≪≫
    (Functor.associator _ _ _).symm

/-- 主導来shiftとの自然比較を、既存の充満部分圏としてのPerfへ持ち上げる。 -/
def perfectDGModuleShiftHomotopyPerfectIso (S : Set D) (s : ℤ) :
    (perfectDGModuleShiftDG A D S s).onHomotopy ⋙ perfectDGModuleToPerfect A D S ≅
      perfectDGModuleToPerfect A D S ⋙ shiftFunctor (PerfectModuleCategoryOver A D S) s := by
  let I := (modulePerfectOver A D S).ι
  let e := perfectDGModuleToPerfectCompInclusion A D S
  exact ((Functor.FullyFaithful.ofFullyFaithful I).whiskeringRight
    (PerfectDGHomotopyCategoryOver A D S)).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ e ≪≫ perfectDGModuleShiftHomotopyDerivedIso A D S s ≪≫
        Functor.isoWhiskerRight e.symm (shiftFunctor (DerivedModuleCategory A D) s) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (perfectDGModuleToPerfect A D S) (I.commShiftIso s).symm ≪≫
        (Functor.associator _ _ _).symm)

end SerrePositivity.DifferentialGraded

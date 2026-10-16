module
public import SerrePositivity.DifferentialGraded.Category.RestrictionComparison
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
  restrictHomotopyComparisonIso (moduleShiftDG A D s) (modulePerfectProjectiveOver A D S)
    (fun _ h => modulePerfectProjectiveOver_shift A D h s)
    (shiftFunctor (ModuleHomotopyCategory A D) s) (moduleShiftDGHomotopyIso A D s)


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

/-- 主Perfのshift比較を包含で写すと、主導来比較と包含のshift比較の逆の合成になる。 -/
lemma perfectDGModuleShiftHomotopyPerfectIso_hom_inclusion (S : Set D) (s : ℤ)
    (X : PerfectDGHomotopyCategoryOver A D S) :
    (modulePerfectOver A D S).ι.map
      ((perfectDGModuleShiftHomotopyPerfectIso A D S s).hom.app X) =
    (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫
      ((modulePerfectOver A D S).ι.commShiftIso s).inv.app
        ((perfectDGModuleToPerfect A D S).obj X) := by
  suffices h : ((Functor.FullyFaithful.ofFullyFaithful (modulePerfectOver A D S).ι).preimage
      (X := (perfectDGModuleToPerfect A D S).obj
        ((perfectDGModuleShiftDG A D S s).onHomotopy.obj X))
      (Y := ((perfectDGModuleToPerfect A D S).obj X)⟦s⟧)
      (𝟙 ((perfectDGModuleToDerived A D S).obj
        ((perfectDGModuleShiftDG A D S s).onHomotopy.obj X)) ≫
        (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫
        ((modulePerfectOver A D S).ι.commShiftIso s).inv.app
          ((perfectDGModuleToPerfect A D S).obj X))).hom =
      (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫
        ((modulePerfectOver A D S).ι.commShiftIso s).inv.app
          ((perfectDGModuleToPerfect A D S).obj X) by
    simpa [perfectDGModuleShiftHomotopyPerfectIso, Functor.FullyFaithful.preimageIso,
      Functor.FullyFaithful.whiskeringRight, perfectDGModuleToPerfectCompInclusion,
      ObjectProperty.liftCompιIso] using h
  exact ((Functor.FullyFaithful.ofFullyFaithful (modulePerfectOver A D S).ι).map_preimage
      (X := (perfectDGModuleToPerfect A D S).obj
        ((perfectDGModuleShiftDG A D S s).onHomotopy.obj X))
      (Y := ((perfectDGModuleToPerfect A D S).obj X)⟦s⟧)
      (𝟙 _ ≫ (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫
        ((modulePerfectOver A D S).ι.commShiftIso s).inv.app
          ((perfectDGModuleToPerfect A D S).obj X))).trans (Category.id_comp _)

end SerrePositivity.DifferentialGraded

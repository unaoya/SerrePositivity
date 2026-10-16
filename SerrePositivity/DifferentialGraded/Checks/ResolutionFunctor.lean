module
public import SerrePositivity.DifferentialGraded.Derived.ResolutionFunctorChoice
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 指定局所化上の解像度関手と選択の自己/推移整合性 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (M : ModuleCategory A D) :
    (moduleDerivedResolutionFunctor A D R).obj ((moduleToDerived A D).obj M) ≅
      (moduleToHomotopy A D).obj (R M).obj :=
  moduleDerivedResolutionComputation A D R M

example (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionIso A D R S ≪≫ moduleDerivedResolutionIso A D S T =
      moduleDerivedResolutionIso A D R T :=
  moduleDerivedResolutionIso_trans A D R S T

example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    (moduleDerivedResolutionFunctor (ZMod 2) PUnit.{1}
      (moduleCanonicalProjectiveResolution (ZMod 2) PUnit.{1})).obj
        ((moduleToDerived (ZMod 2) PUnit.{1}).obj M) ≅
      (moduleToHomotopy (ZMod 2) PUnit.{1}).obj
        (moduleCanonicalProjectiveResolution (ZMod 2) PUnit.{1} M).obj :=
  moduleDerivedResolutionComputation (ZMod 2) PUnit.{1}
    (moduleCanonicalProjectiveResolution (ZMod 2) PUnit.{1}) M

#print axioms moduleResolutionHomotopyFunctor
#print axioms moduleResolutionHomotopyFunctor_inverts
#print axioms moduleDerivedResolutionFunctor
#print axioms moduleDerivedResolutionFunctor_lifting
#print axioms moduleDerivedResolutionFunctor_fac
#print axioms moduleDerivedResolutionComputation
#print axioms moduleResolutionHomotopyIso
#print axioms moduleResolutionHomotopyIso_hom_app
#print axioms moduleResolutionHomotopyIso_self
#print axioms moduleResolutionHomotopyIso_trans
#print axioms moduleDerivedResolutionIso
#print axioms moduleDerivedResolutionIso_hom_app
#print axioms moduleDerivedResolutionIso_self
#print axioms moduleDerivedResolutionIso_trans

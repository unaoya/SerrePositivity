module
public import SerrePositivity.DifferentialGraded.Derived.RightTensorLeftFunctor
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 左加群の射による導来tensor自然変換の受入検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {L L' : LeftModuleCategory A D} (g : L ⟶ L') (M : ModuleCategory A D) :
    (rightTensorHomotopyLeftMap A D g).app ((moduleToHomotopy A D).obj M) =
      (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map (map A D (𝟙 M) g) :=
  rightTensorHomotopyLeftMap_app A D g M

section
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
example (L : LeftModuleCategory A D) :
    (moduleDerivedTensorLeftFunctor A D).obj L =
      moduleDerivedTensorRight A D (ForgetEnrichment.to (Complex A) L) :=
  moduleDerivedTensorLeftFunctor_obj A D L

example {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    {X Y : DerivedModuleCategory A D} (f : X ⟶ Y) :
    ((moduleDerivedTensorLeftFunctor A D).obj L).map f ≫
        ((moduleDerivedTensorLeftFunctor A D).map g).app Y =
      ((moduleDerivedTensorLeftFunctor A D).map g).app X ≫
        ((moduleDerivedTensorLeftFunctor A D).obj L').map f :=
  ((moduleDerivedTensorLeftFunctor A D).map g).naturality f
end

example {L L' : LeftModuleCategory (ZMod 2) PUnit.{1}} (g : L ⟶ L')
    (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    (rightTensorHomotopyLeftMap (ZMod 2) PUnit.{1} g).app
        ((moduleToHomotopy (ZMod 2) PUnit.{1}).obj M) =
      (_root_.HomotopyCategory.quotient (ModuleCat.{0} (ZMod 2)) (.up ℤ)).map
        (map (ZMod 2) PUnit.{1} (𝟙 M) g) :=
  rightTensorHomotopyLeftMap_app (ZMod 2) PUnit.{1} g M

#print axioms rightTensorLeftMap
#print axioms rightTensorLeftMap_id
#print axioms rightTensorLeftMap_comp
#print axioms rightTensorHomotopyLeftMap
#print axioms rightTensorHomotopyLeftMap_app
#print axioms rightTensorHomotopyLeftMap_id
#print axioms rightTensorHomotopyLeftMap_comp
#print axioms rightTensorHomotopyBifunctor
#print axioms moduleResolutionDerivedTensorLeftFunctor
#print axioms moduleResolutionDerivedTensorLeftFunctor_obj
#print axioms moduleResolutionDerivedTensorLeftFunctor_map_app
#print axioms moduleDerivedTensorLeftFunctor
#print axioms moduleDerivedTensorLeftFunctor_obj

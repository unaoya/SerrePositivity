module
public import SerrePositivity.DifferentialGraded.Bimodule.ExplicitRightModuleFunctor
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionUncurry
public import Mathlib.Data.ZMod.Basic

/-! # 明示的uncurry表示の同型と左右制限Homの検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensorModule
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

-- 対象宇宙を独立に保ち、局所K-flat性を要求しない。
example : uncurryFunctor A B C ⋙ functor A B C ≅ 𝟭 (BimoduleCategory A B C) :=
  uncurryCounitIso A B C

example : rightModuleFunctor A B C ≅ (rightModuleBimoduleEquivalence A B C).inverse :=
  rightModuleInverseIso A B C

example {M N : BimoduleCategory A B C} (f : M ⟶ N) (b : B) (c : C) :
    (moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (Opposite.op (Opposite.op b, c))).map
        ((rightModuleFunctor A B C).map f) =
      (BimoduleCategory.valueEvaluation A B C b c).map f :=
  rightModuleFunctor_map_value A B C f b c

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] :
    rightModuleFunctor (ZMod 2) X Y ≅
      (rightModuleBimoduleEquivalence (ZMod 2) X Y).inverse :=
  rightModuleInverseIso (ZMod 2) X Y

namespace SerrePositivity.DifferentialGraded
#print axioms BimoduleTensorModule.uncurryMap
#print axioms BimoduleTensorModule.uncurryMap_eval
#print axioms BimoduleTensorModule.uncurryFunctor
#print axioms BimoduleTensorModule.uncurryRightCounitIso
#print axioms BimoduleTensorModule.uncurryRightCounitIso_hom_eval
#print axioms BimoduleTensorModule.uncurryRightCounitIso_naturality
#print axioms BimoduleTensorModule.uncurryObjectCounitIso
#print axioms BimoduleTensorModule.uncurryObjectCounitIso_hom_value
#print axioms BimoduleTensorModule.uncurryCounitIso
#print axioms BimoduleTensorModule.rightModuleFunctor
#print axioms BimoduleTensorModule.rightModuleFunctor_map_value
#print axioms BimoduleTensorModule.rightModuleCounitIso
#print axioms BimoduleTensorModule.rightModuleInverseIso
#print axioms Bimodule.leftRestriction_uncurryHom
#print axioms Bimodule.rightRestriction_uncurryHom
end SerrePositivity.DifferentialGraded

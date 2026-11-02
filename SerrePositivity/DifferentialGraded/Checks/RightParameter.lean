module
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import Mathlib.Data.ZMod.Basic

/-! # 右パラメータ付きbalanced tensorの普遍性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

example (M : RightModule A D) (N : LeftModule A D) (K T : Complex A)
    (a : RightParamFamily A D M N K T) : BalancedFamily A D M N (homComplex A K T) :=
  curryRightParamFamily A D M N a

example [Small.{u} D] (M : RightModule A D) (N : LeftModule A D) (K T : Complex A) :
    (obj A D M N ⊗ K ⟶ T) ≃ RightParamFamily A D M N K T := rightParamHomEquiv A D M N K T

example (M : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1})
    (K T : Complex (ZMod 2)) :
    (obj (ZMod 2) PUnit.{1} M N ⊗ K ⟶ T) ≃ RightParamFamily (ZMod 2) PUnit.{1} M N K T :=
  rightParamHomEquiv (ZMod 2) PUnit.{1} M N K T

#print axioms RightParamFamily
#print axioms curryRightParamFamily
#print axioms rightParamDesc
#print axioms ι_rightParamDesc
#print axioms rightParam_hom_ext
#print axioms rightParamRestrict
#print axioms rightParamHomEquiv
#print axioms paramDesc_element
#print axioms rightParamDesc_element
#print axioms paramDesc_curry_element

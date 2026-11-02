module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import Mathlib.Data.ZMod.Basic

/-! # 左加群変数のbalanced tensorの余極限保存 -/
@[expose] public section
noncomputable section
universe u v w t
open CategoryTheory CategoryTheory.Limits SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : LeftModuleCategory A D ≌ ModuleCategory A Dᵒᵖ := leftRightOppositeEquivalence A D

example (M : RightModule A D) :
    leftTensorFunctor A D M ≅ leftModuleToRightOpposite A D ⋙
      rightTensorFunctor A Dᵒᵖ M.toFunctor := leftTensorSwapIso A D M

example (M : RightModule A D) :
    PreservesColimitsOfSize.{w, t} (leftTensorFunctor A D M) := inferInstance

example (M : RightModule (ZMod 2) PUnit.{1}) :
    PreservesColimitsOfSize.{w, t} (leftTensorFunctor (ZMod 2) PUnit.{1} M) := inferInstance

#print axioms leftModuleToRightOppositeFullyFaithful
#print axioms leftModuleToRightOppositeEssSurj
#print axioms leftModuleToRightOppositeIsEquivalence
#print axioms leftRightOppositeEquivalence
#print axioms leftModuleToRightOpposite_map_eval
#print axioms swapHom_naturality_left
#print axioms leftTensorFunctor
#print axioms leftTensorSwapIso
#print axioms leftTensorFunctor_preservesColimits

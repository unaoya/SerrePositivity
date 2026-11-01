module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import Mathlib.Data.ZMod.Basic

/-! # balanced tensor–Hom随伴の受入検査 -/
@[expose] public section
noncomputable section
universe u v w t
open CategoryTheory CategoryTheory.Limits SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (N : LeftModule A D) :
    BalancedTensor.rightTensorFunctor A D N ⊣ homRightFunctor A D N :=
  BalancedTensor.tensorHomAdjunction A D N

example (M : ModuleCategory A D) (N : LeftModule A D) (T : Complex A) :
    (BalancedTensor.obj A D (ForgetEnrichment.to (Complex A) M) N ⟶ T) ≃
      (M ⟶ ForgetEnrichment.of (Complex A) (homRightModule A D N T)) :=
  BalancedTensor.tensorHomEquiv A D M N T

-- 図式のサイズを環・対象の宇宙と独立に指定し、存在する余極限の保存を検査する。
example (N : LeftModule A D) :
    PreservesColimitsOfSize.{w, t} (BalancedTensor.rightTensorFunctor A D N) := inferInstance

example (N : LeftModule (ZMod 2) PUnit.{1}) :
    BalancedTensor.rightTensorFunctor (ZMod 2) PUnit.{1} N ⊣
      homRightFunctor (ZMod 2) PUnit.{1} N :=
  BalancedTensor.tensorHomAdjunction (ZMod 2) PUnit.{1} N

#print axioms BalancedTensor.familyElement
#print axioms BalancedTensor.balancedFamily_element
#print axioms BalancedTensor.balancedFamilyMk
#print axioms BalancedTensor.curryBalancedFamily_action
#print axioms BalancedTensor.curryBalancedFamily
#print axioms BalancedTensor.uncurryModuleMapFamily
#print axioms BalancedTensor.balancedFamilyMapEquiv
#print axioms BalancedTensor.tensorHomEquiv
#print axioms BalancedTensor.tensorHomEquiv_eval
#print axioms BalancedTensor.ι_tensorHomEquiv_symm
#print axioms BalancedTensor.tensorHomEquiv_naturality_target
#print axioms BalancedTensor.tensorHomEquiv_naturality_source
#print axioms BalancedTensor.rightTensorFunctor
#print axioms BalancedTensor.tensorHomAdjunction
#print axioms BalancedTensor.tensorHomAdjunction_homEquiv
#print axioms BalancedTensor.tensorHomAdjunction_unit
#print axioms BalancedTensor.tensorHomAdjunction_unit_eval
#print axioms BalancedTensor.tensorHomAdjunction_counit
#print axioms BalancedTensor.ι_tensorHomAdjunction_counit
#print axioms BalancedTensor.tensorHomAdjunction_counit_element
#print axioms BalancedTensor.tensorHomAdjunction_left_triangle
#print axioms BalancedTensor.tensorHomAdjunction_right_triangle
#print axioms BalancedTensor.rightTensorFunctor_preservesColimits

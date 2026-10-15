module
public import SerrePositivity.DifferentialGraded.Module.HomRightContraMaps
public import Mathlib.Data.ZMod.Basic

/-! # 左加群変数の反変右Hom dg関手の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory CochainComplex HomComplex SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (T : Complex A) : DGFunctor A (LeftModule A D)ᵒᵖ (RightModule A D) :=
  homRightContraDG A D T

example (T : Complex A) : (LeftModuleCategory A D)ᵒᵖ ⥤ ModuleCategory A D :=
  homRightContraFunctor A D T

example (N N' : LeftModule A D) (T : Complex A) (x : D)
    (τ : (leftModuleHom A D N N').X (-1)) (g : Homogeneous (N'.obj x) T 1) :
    (((moduleHomπ A D (homRightModule A D N' T) (homRightModule A D N T) x).f (-1)
      ((homRightContraHomMap A D N N' T).f (-1) τ)).v 1 0 (by omega)) g =
    -(((leftModuleHomπ A D N N' x).f (-1) τ).comp g (by omega)) := by
  simpa using homRightContraHomMap_element A D N N' T x (by omega : 1 + (-1) = 0) τ g

example (T : Complex (ZMod 2)) :
    DGFunctor (ZMod 2) (LeftModule (ZMod 2) PUnit.{1})ᵒᵖ (RightModule (ZMod 2) PUnit.{1}) :=
  homRightContraDG (ZMod 2) PUnit.{1} T

#print axioms homRightContraEvaluation
#print axioms homRightContraApp
#print axioms homRightContraApp_element
#print axioms homRightContra_action
#print axioms homRightContraParam
#print axioms homRightContraHomMap
#print axioms homRightContraHomMap_π
#print axioms homRightContraHomMap_element
#print axioms homRightContraHomMap_π_apply
#print axioms homRightContraHomMap_unit
#print axioms homRightContraHomMap_forward
#print axioms homRightContraDG
#print axioms homContravariantDG_closedMap
#print axioms leftModuleEvaluation_closedMap
#print axioms homRightContraHomMap_closed_component
#print axioms homRightContraFunctor
#print axioms homRightContraFunctor_map_eval

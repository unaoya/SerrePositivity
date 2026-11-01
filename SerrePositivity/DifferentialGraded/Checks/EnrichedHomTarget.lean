module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import Mathlib.Data.ZMod.Basic

/-! # 右Hom加群のdg関手性と終域の全Hom自然性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory CochainComplex HomComplex SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

example (N : LeftModule A D) (T T' : Complex A) :
    ModuleParamTrans A D (homComplex A T T') (homRightModule A D N T)
      (homRightModule A D N T') := homRightParam A D N T T'

example [Small.{u} D] (N : LeftModule A D) : DGFunctor A (Complex A) (RightModule A D) :=
  homRightDG A D N

-- 負次数の後合成に追加の符号が付かないことを検査する。
example (P T T' : Complex A) (f : Homogeneous T T' (-1)) (g : Homogeneous P T 1) :
    (((homCovariantDG A P).map T T').f (-1) f).v 1 0 (by omega) g =
      g.comp f (by omega) := homCovariantDG_map_element A P T T' (-1) 1 0 (by omega) f g

example (N : LeftModule (ZMod 2) PUnit.{1}) :
    DGFunctor (ZMod 2) (Complex (ZMod 2)) (RightModule (ZMod 2) PUnit.{1}) :=
  homRightDG (ZMod 2) PUnit.{1} N

#print axioms homCovariantDG
#print axioms homCovariantDG_map_element
#print axioms homCovariantDG_closedMap
#print axioms homRightPostcompose_action
#print axioms homRightParam
#print axioms homRightHomMap
#print axioms homRightHomMap_π
#print axioms homRightHomMap_element
#print axioms homRightHomMap_π_apply
#print axioms homRightHomMap_unit
#print axioms homRightHomMap_forward
#print axioms homRightDG
#print axioms homRightHomMap_closedMap
#print axioms curryRight_twice_apply
#print axioms curryRight_associator_apply
#print axioms BalancedTensor.enrichedTensorHomIso_hom_element
#print axioms BalancedTensor.enrichedTensorHomIso_target_naturality

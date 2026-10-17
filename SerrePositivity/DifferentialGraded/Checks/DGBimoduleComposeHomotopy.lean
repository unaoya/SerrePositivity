module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleHomotopy
public import Mathlib.Data.ZMod.Basic

/-! # flat条件なしの合成後のホモトピー同一視と増大squareの検査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]

-- 前因子とsource加群のK-flat性・射影性を一切仮定しない。
example (P : BimoduleCategory A B C)
    (M : ModuleCategory A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ) :
    BimoduleCategory.quasiIso A B E ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map
        (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π)) :=
  composeAfter_sourcePrecylinderProjection_quasiIso A B C E P M

example (P : BimoduleCategory A B C) {Q Q' : BimoduleCategory A C E} (f g : Q ⟶ Q')
    (h : (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map f) =
      (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map g)) :
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map f) =
      (bimoduleToDerived A B E).map ((composeAfter A B C E P).map g) :=
  composeAfter_map_eq_of_inverse_source_homotopy A B C E P f g h

example (X : Type v) (Y : Type w) (Z : Type z)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y] [DGCategory (ZMod 2) Z]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] (P : BimoduleCategory (ZMod 2) X Y)
    (M : ModuleCategory (ZMod 2) (DGTensorCategory (ZMod 2) Yᵒᵖ Z)ᵒᵖ) :
    BimoduleCategory.quasiIso (ZMod 2) X Z ((composeAfter (ZMod 2) X Y Z P).map
      ((rightModuleBimoduleEquivalence (ZMod 2) Y Z).functor.map
        (modulePrecylinder (ZMod 2) (DGTensorCategory (ZMod 2) Yᵒᵖ Z)ᵒᵖ M).π)) :=
  composeAfter_sourcePrecylinderProjection_quasiIso (ZMod 2) X Y Z P M

namespace SerrePositivity.DifferentialGraded
#print axioms rightModuleBimoduleRightRestrictionNatIso
#print axioms rightModuleBimoduleRightRestrictionNatIso_app
#print axioms BalancedTensor.tensorModuleHom_naturality
#print axioms BalancedTensor.rightTensor_intervalProjection_quasiIso
#print axioms BalancedTensor.rightTensor_precylinderProjection_quasiIso
#print axioms moduleRestrictionTensorIso_hom_eval
#print axioms moduleRestriction_precylinderProjection
#print axioms rightTensor_restrictedPrecylinderProjection_quasiIso
#print axioms BimoduleTensor.composeAfter
#print axioms BimoduleTensor.rightTensor_bimoduleSourcePrecylinderProjection_quasiIso
#print axioms BimoduleTensor.composeAfter_sourcePrecylinderProjection_quasiIso
#print axioms BimoduleTensor.composeAfter_equalizes_source_boundary
#print axioms BimoduleTensor.composeAfter_map_eq_of_source_homotopy
#print axioms BimoduleTensor.composeAfter_map_eq_of_inverse_source_homotopy
#print axioms BimoduleTensor.middleRestrictionResolvedMap_eq_of_source_homotopy
#print axioms BimoduleTensor.middleRestrictionResolvedMap_comp_of_source_homotopy
end SerrePositivity.DifferentialGraded

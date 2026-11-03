module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence
public import Mathlib.Data.ZMod.Basic

/-! # flat条件なしの合成後のホモトピー同一視と増大squareの検査

## 概要
flat条件なしの合成後のホモトピー同一視と増大squareの検査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
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

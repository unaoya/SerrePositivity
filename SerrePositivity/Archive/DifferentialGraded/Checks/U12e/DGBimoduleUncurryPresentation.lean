module
public import SerrePositivity.DifferentialGraded.Bimodule.ExplicitRightModuleFunctor
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionUncurry
public import Mathlib.Data.ZMod.Basic

/-! # 明示的uncurry表示の同型と左右制限Homの検査

## 概要
明示的uncurry表示の同型と左右制限Homの検査。

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

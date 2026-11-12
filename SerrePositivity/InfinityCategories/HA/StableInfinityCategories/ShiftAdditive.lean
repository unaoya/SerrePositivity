module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyPreadditive
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Shift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # 安定ホモトピー圏のシフトの加法性

概要：suspension・loop と全整数シフトは h C の加法関手である。
方針：自己同値が二項積と零射を保つことから加法性を得る。
規約：既存のシフトと前加法構造を使う。使われ方：回転三角形と Pretriangulated。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定ホモトピー圏の suspension 関手は加法的である。
方針：suspension 自己同値の二項積と零射の保存を使う。
規約：構成済みの suspensionFunctor。使われ方：接続射の加法的な計算。 -/
instance suspensionFunctor_additive {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).Additive := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionEquivalence X).functor.Additive
  exact Functor.additive_of_preserves_binary_products _

/-- 概要：安定ホモトピー圏の loop 関手は加法的である。
方針：suspension 自己同値の逆関手の加法性を使う。
規約：構成済みの loopFunctor。使われ方：負のシフトと fiber 列。 -/
instance loopFunctor_additive {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor X).Additive := by
  have : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionEquivalence X).functor.Additive := suspensionFunctor_additive
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionEquivalence X).inverse_additive

/-- 概要：安定ホモトピー圏の全ての整数シフトは加法的である。
方針：各整数シフトの自己同値性から二項積と零射の保存を得る。
規約：元の HasShift ℤ を変更しない。使われ方：三角形の回転と三角関手。 -/
instance shiftFunctor_additive_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (n : ℤ) :
    (shiftFunctor (hoFunctor.obj X) n).Additive :=
  Functor.additive_of_preserves_binary_products _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceIntegerShift

/-! # 安定 ∞ 圏のホモトピー圏の整数シフト

概要：suspension 自己同値から h C の整数シフトを構成する。
方針：自己同値の整数シフトを適用し、一回シフトを既存の Σ と自然同型で比較する。
規約：前加法構造とシフトの加法性は別に証明する。
使われ方：S4 の Mathlib の三角形と三角構造。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定 ∞ 圏のホモトピー圏は整数シフトを持つ。
方針：構成済みの suspension 自己同値から全整数の整合的なシフトを得る。
規約：単位・加法・結合の整合条件を含む。使われ方：通常の三角形の値域。 -/
instance hasShift_ho (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    HasShift (hoFunctor.obj X) ℤ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEquivalenceHasShift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionEquivalence X)

/-- 概要：h C の一回シフトは既存の suspension 関手と自然同型。
方針：自己同値からのシフトの一回の比較を適用する。
規約：Σ の元の定義を変更しない。使われ方：接続射を通常の三角形の第三射にする。 -/
def shiftOneSuspensionIso (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    shiftFunctor (hoFunctor.obj X) (1 : ℤ) ≅ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEquivalenceShiftOneIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionEquivalence X)

/-- 概要：h C の負の一回シフトは既存の loop 関手と自然同型。
方針：一回シフトと Σ の自然同型を自己同値の逆関手に移す。
規約：Ω の元の定義を変更しない。使われ方：負のシフトの解釈。 -/
def shiftNegOneLoopIso (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    shiftFunctor (hoFunctor.obj X) (-1 : ℤ) ≅ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor X :=
  Iso.isoInverseOfIsoFunctor (G := shiftEquiv (hoFunctor.obj X) (1 : ℤ))
    (G' := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionEquivalence X) (shiftOneSuspensionIso X)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

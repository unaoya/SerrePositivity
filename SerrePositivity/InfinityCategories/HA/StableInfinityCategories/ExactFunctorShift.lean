module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorSuspension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Shift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ShiftCommutationInteger

/-! # 完全関手と整数シフトの交換

概要：安定 ∞ 圏の完全関手が誘導する h C の関手に CommShift ℤ を構成する。
方針：懸垂比較を一回シフトの比較へ移し、整数冪による整合的な延長を適用する。
規約：始域・終域の既存の HasShift を使う。使われ方：三角関手の公開。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Functor SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

variable {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
  [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]

/-- 概要：完全関手の h の関手は一回シフトと交換する。
方針：シフトと懸垂の自然同型で懸垂比較を挟む。
規約：Mathlib の CommShift の向き。使われ方：整数シフトとの交換の生成元。 -/
def exactFunctorShiftOneIso :
    shiftFunctor (hoFunctor.obj X) (1 : ℤ) ⋙ (hoFunctor.map F).toFunctor ≅
      (hoFunctor.map F).toFunctor ⋙ shiftFunctor (hoFunctor.obj Y) (1 : ℤ) :=
  isoWhiskerRight (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X) (hoFunctor.map F).toFunctor ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionIso F ≪≫
      isoWhiskerLeft (hoFunctor.map F).toFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso Y).symm

/-- 概要：完全関手の h の関手は整数シフトと整合的に交換する。
方針：一回シフトの比較を交換同型群の整数冪により延長する。
規約：全ての CommShift の整合条件を含む。使われ方：Mathlib の三角関手。 -/
instance exactFunctorCommShift : (hoFunctor.map F).toFunctor.CommShift ℤ :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableCommShiftOfOne (exactFunctorShiftOneIso F)

/-- 概要：完全関手の CommShift の一回比較は構成した懸垂比較から得られる。
方針：整合的な延長が生成元を復元することを使う。
規約：厳密な同型の等式。使われ方：cofiber 三角形の第三射。 -/
lemma exactFunctorCommShift_one :
    (hoFunctor.map F).toFunctor.commShiftIso (1 : ℤ) = exactFunctorShiftOneIso F :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableCommShiftOfOne_one (exactFunctorShiftOneIso F)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

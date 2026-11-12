module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.SSetPullbackAdjoint
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalPullbackAnodyne

/-!
概要：left fibration に沿う任意の right anodyne な射の引き戻しは right anodyne。
方針：通常の前層圏の依存積の存在で中間定理の右随伴の仮定を解消する。
規約：任意の宇宙の単体集合。quasicategory 性を別に要求しない。
使われ方：Kerodon Proposition 7.2.3.10（Tag 02P6） の left fibration の場合と Quillen A の還元。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：left fibration の slice 引き戻し関手は right anodyne な射を保つ。
方針：引き戻し関手の右随伴を前層圏の一般定理で与える。
規約：追加の一般圏論的仮定を残さない。
使われ方：通常の slice における right anodyne 性の移送。 -/
lemma leftFibration_overPullback_rightAnodyne {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {A D : Over B} (i : A ⟶ D)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions ((Over.pullback p).map i).left := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalSSetPullback_isLeftAdjoint p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_overPullback_rightAnodyne_of_isLeftAdjoint p i hi

/-- 概要：left fibration に沿う任意の right anodyne な射の引き戻しは right anodyne。
方針：全右ホーンでの検査を通常の依存積随伴によって全ての right anodyne な射へ移す。
規約：始域・底・全空間の quasicategory 性は不要。
使われ方：right cofinality の引き戻しの安定性と Quillen A。 -/
lemma leftFibration_pullback_rightAnodyne {E A B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (pullback.fst p f) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalSSetPullback_isLeftAdjoint p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_pullback_rightAnodyne_of_isLeftAdjoint p f hf

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

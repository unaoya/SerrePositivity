module

public import SerrePositivity.InfinityCategories.F1B.SSetPullbackAdjoint
public import SerrePositivity.InfinityCategories.F1B.CofinalPullbackAnodyne

/-!
概要：left fibration に沿う任意の right anodyne な射の引き戻しは right anodyne。
方針：通常の前層圏の依存積の存在で中間定理の右随伴の仮定を解消する。
規約：任意の宇宙の単体集合。quasicategory 性を別に要求しない。
使われ方：Kerodon Proposition 7.2.3.10 の left fibration の場合と Quillen A の還元。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：left fibration の slice 引き戻し関手は right anodyne な射を保つ。
方針：引き戻し関手の右随伴を前層圏の一般定理で与える。
規約：追加の一般圏論的仮定を残さない。
使われ方：通常の slice における right anodyne 性の移送。 -/
lemma leftFibration_overPullback_rightAnodyne {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {A D : Over B} (i : A ⟶ D)
    (hi : rightAnodyneExtensions i.left) :
    rightAnodyneExtensions ((Over.pullback p).map i).left := by
  have := cofinalSSetPullback_isLeftAdjoint p
  exact leftFibration_overPullback_rightAnodyne_of_isLeftAdjoint p i hi

/-- 概要：left fibration に沿う任意の right anodyne な射の引き戻しは right anodyne。
方針：全右ホーンでの検査を通常の依存積随伴によって全ての right anodyne な射へ移す。
規約：始域・底・全空間の quasicategory 性は不要。
使われ方：right cofinality の引き戻しの安定性と Quillen A。 -/
lemma leftFibration_pullback_rightAnodyne {E A B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (f : A ⟶ B) (hf : rightAnodyneExtensions f) :
    rightAnodyneExtensions (pullback.fst p f) := by
  have := cofinalSSetPullback_isLeftAdjoint p
  exact leftFibration_pullback_rightAnodyne_of_isLeftAdjoint p f hf

end SerrePositivity.InfinityCategories

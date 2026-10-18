module

public import SerrePositivity.KST.Descent.SplitCech
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 実際の増強 Čech nerve と幾何的な引き戻し

## 概要
増強 Čech nerve 関手が引き戻しを保つことを証明し、底変換した射の Čech 図式へ適用する。

## 方針
Arrow の極限を両端で検査し、増強 Čech nerve の既存の右随伴性を使う。

## 規約
幾何的な通常の極限に関する証明であり、前層の値域の Tot の Fubini は別に必要。

## 使われ方
論文 補題 3.2 の τ 位相の層論を Čech 計算で置換する際の底変換比較。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C]

/-- 概要：Arrow の Cartesian 性は両端で検査できる（論文 補題 3.2）。
方針：Comma の二射影が共同で極限を反映することを使う。
規約：可換性と始域・終域の実際の引き戻しを検査する。
使われ方：底変換した射を Arrow 内の実際の引き戻しにする。 -/
theorem arrow_isPullback_of_components {P X Y B : Arrow C}
    (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ B) (g : Y ⟶ B)
    (comm : p ≫ f = q ≫ g)
    (left : IsPullback p.left q.left f.left g.left)
    (right : IsPullback p.right q.right f.right g.right) : IsPullback p q f g := by
  apply IsPullback.of_isLimit' ⟨comm⟩
  apply Comma.fstSndJointlyReflectLimit
  · exact (PullbackCone.isLimitMapConeEquiv _ (Comma.fst (𝟭 C) (𝟭 C))).symm left.isLimit
  · exact (PullbackCone.isLimitMapConeEquiv _ (Comma.snd (𝟭 C) (𝟭 C))).symm right.isLimit

variable [HasFiniteLimits C]

/-- 概要：増強 Čech nerve 関手は引き戻しを保つ（論文 補題 3.2）。
方針：増強対象から射を取る関手への右随伴性から極限保存を得る。
規約：値域は実際の増強単体対象の圏。
使われ方：二重 Čech の行を底変換の引き戻しとして比較する。 -/
noncomputable instance augmentedCechNerve_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (SimplicialObject.augmentedCechNerve (C := C)) :=
  SimplicialObject.cechNerveAdjunction.rightAdjoint_preservesLimits.preservesLimitsOfShape

variable {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)

/-- 概要：底変換した射から元の射への Arrow の射（論文 補題 3.2）。
方針：実際の引き戻しの第一射影と基底変更の射を使う。
規約：底変換の射は第二射影とする。
使われ方：元の Čech 図式への指定比較。 -/
noncomputable def baseChangeArrowToOriginal :
    Arrow.mk (pullback.snd f g) ⟶ Arrow.mk f :=
  Arrow.homMk (pullback.fst f g) g pullback.condition

/-- 概要：底変換した射から新しい基底の恒等射への Arrow の射（論文 補題 3.2）。
方針：第二射影と恒等射で正方形を作る。
規約：始域側の射も底変換の指定射そのもの。
使われ方：底変換の Cartesian 正方形。 -/
noncomputable def baseChangeArrowToIdentity :
    Arrow.mk (pullback.snd f g) ⟶ Arrow.mk (𝟙 Z) :=
  Arrow.homMk (pullback.snd f g) (𝟙 Z)

/-- 概要：Arrow 内の実際の底変換正方形（論文 補題 3.2）。
方針：始域側は元の引き戻し、終域側は恒等射の引き戻しであることを検査する。
規約：底変換した射と元の射を含む指定四辺。
使われ方：増強 Čech nerve 関手による底変換比較。 -/
theorem baseChangeArrow_isPullback :
    IsPullback (baseChangeArrowToOriginal f g) (baseChangeArrowToIdentity f g)
      (Arrow.homMk f (𝟙 Y) : Arrow.mk f ⟶ Arrow.mk (𝟙 Y))
      (Arrow.homMk g g : Arrow.mk (𝟙 Z) ⟶ Arrow.mk (𝟙 Y)) := by
  apply arrow_isPullback_of_components
  · apply Arrow.hom_ext
    · exact pullback.condition
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact IsPullback.of_hasPullback f g
  · exact (IsPullback.of_id_fst (f := g)).flip

/-- 概要：底変換した射の増強 Čech 図式は実際の引き戻し（論文 補題 3.2）。
方針：Arrow の指定 Cartesian 正方形に増強 Čech nerve 関手を適用する。
規約：前層が引き戻しを保つことは仮定していない。
使われ方：二重 Čech の幾何的な底変換比較と細分の入力。 -/
theorem baseChangeAugmentedCech_isPullback :
    IsPullback (Arrow.mapAugmentedCechNerve (baseChangeArrowToOriginal f g))
      (Arrow.mapAugmentedCechNerve (baseChangeArrowToIdentity f g))
      (Arrow.mapAugmentedCechNerve
        (Arrow.homMk f (𝟙 Y) : Arrow.mk f ⟶ Arrow.mk (𝟙 Y)))
      (Arrow.mapAugmentedCechNerve
        (Arrow.homMk g g : Arrow.mk (𝟙 Z) ⟶ Arrow.mk (𝟙 Y))) :=
  (baseChangeArrow_isPullback f g).map SimplicialObject.augmentedCechNerve

end SerrePositivity.KST.Descent

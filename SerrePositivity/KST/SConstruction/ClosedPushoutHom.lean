module
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # 閉 Hom の全パラメータを保つ押し出し降下
概要：押し出しの両脚で整合する全内部 Hom 族を、元の押し出しの内部 Hom へ降ろす。
方針：右 tensor の余極限保存と curry を使う。
規約：任意の braided 閉モノイダル圏。使われ方：点つき実押し出しの厳密豊穣作用。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed Limits
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]
variable {W X Y Z P : C} (f : W ⟶ X) (g : W ⟶ Y) [HasPushout f g]

omit [HasPushout f g] [BraidedCategory C] in
/-- 全内部 Hom の整合条件は、同じ元の評価の tensor した整合条件を与える。 -/
lemma closedPushoutHom_condition (a : P ⟶ (ihom X).obj Z) (b : P ⟶ (ihom Y).obj Z)
    (h : a ≫ (pre f).app Z = b ≫ (pre g).app Z) :
    f ▷ P ≫ uncurry a = g ▷ P ≫ uncurry b := by
  simpa only [uncurry_pre_app] using congrArg uncurry h

/-- 元の押し出しの、同じ全パラメータの閉 Hom への実降下。 -/
def closedPushoutHomDesc (a : P ⟶ (ihom X).obj Z) (b : P ⟶ (ihom Y).obj Z)
    (h : a ≫ (pre f).app Z = b ≫ (pre g).app Z) : P ⟶ (ihom (pushout f g)).obj Z :=
  curry (((tensorRight P).map_isPushout (IsPushout.of_hasPushout f g)).desc
    (uncurry a) (uncurry b) (closedPushoutHom_condition f g a b h))

/-- 降下した全内部 Hom は、元の左脚で同じ全入力族を回収する。 -/
lemma closedPushoutHomDesc_inl (a : P ⟶ (ihom X).obj Z) (b : P ⟶ (ihom Y).obj Z)
    (h : a ≫ (pre f).app Z = b ≫ (pre g).app Z) :
    closedPushoutHomDesc f g a b h ≫ (pre (pushout.inl f g)).app Z = a := by
  apply uncurry_injective
  rw [uncurry_pre_app, closedPushoutHomDesc, uncurry_curry]
  exact ((tensorRight P).map_isPushout (IsPushout.of_hasPushout f g)).inl_desc _ _ _

/-- 降下した全内部 Hom は、元の右脚で同じ全入力族を回収する。 -/
lemma closedPushoutHomDesc_inr (a : P ⟶ (ihom X).obj Z) (b : P ⟶ (ihom Y).obj Z)
    (h : a ≫ (pre f).app Z = b ≫ (pre g).app Z) :
    closedPushoutHomDesc f g a b h ≫ (pre (pushout.inr f g)).app Z = b := by
  apply uncurry_injective
  rw [uncurry_pre_app, closedPushoutHomDesc, uncurry_curry]
  exact ((tensorRight P).map_isPushout (IsPushout.of_hasPushout f g)).inr_desc _ _ _

/-- 元の二脚への制限は、全パラメータの閉 Hom の等号を検出する。 -/
lemma closedPushoutHom_ext {a b : P ⟶ (ihom (pushout f g)).obj Z}
    (hl : a ≫ (pre (pushout.inl f g)).app Z = b ≫ (pre (pushout.inl f g)).app Z)
    (hr : a ≫ (pre (pushout.inr f g)).app Z = b ≫ (pre (pushout.inr f g)).app Z) : a = b := by
  apply uncurry_injective
  apply ((tensorRight P).map_isPushout (IsPushout.of_hasPushout f g)).hom_ext
  · change pushout.inl f g ▷ P ≫ uncurry a = pushout.inl f g ▷ P ≫ uncurry b
    simpa only [uncurry_pre_app] using congrArg uncurry hl
  · change pushout.inr f g ▷ P ≫ uncurry a = pushout.inr f g ▷ P ≫ uncurry b
    simpa only [uncurry_pre_app] using congrArg uncurry hr

end SerrePositivity.KST.SConstruction

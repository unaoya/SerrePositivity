module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TwoSidedGrothendieckHomComponents
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TwoSidedGrothendieckFunctoriality

/-!
# 元の両係数比較の左右の成分の回収

概要：元の係数比較の左右の射成分は元の係数関手の射作用と端点移送で一致する。
方針：Cat の関手の等式による成分の移送を異種等式で吸収する。
規約：元の全圏の射と元の両係数自然変換を保持する。
使われ方：DK9.5の元の比較射の係数自然性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck
open CategoryTheory Opposite

lemma catEqToHom_app_comp_heq {C D : Cat.{u, u}} {H K : C ⟶ D} (h : H = K)
    (A : C) {B : D} (f : K.toFunctor.obj A ⟶ B) :
    HEq ((eqToHom h).toNatTrans.app A ≫ f) f := by
  cases h
  simp

lemma unop_catEqToHom_app_comp_heq {C : Cat.{u, u}} {D : Type u} [Category.{u} D]
    {H K : C ⟶ Cat.of Dᵒᵖ} (h : H = K) (A : C) {B : Dᵒᵖ}
    (f : K.toFunctor.obj A ⟶ B) :
    HEq (((eqToHom h).toNatTrans.app A ≫ f).unop) f.unop := by
  cases h
  simp

variable {W : Type u} [Category.{u} W]
  {F F' : Wᵒᵖ ⥤ Cat.{u, u}} {G G' : W ⥤ Cat.{u, u}}

lemma coefficientMap_leftMap_heq (α : F ⟶ F') (β : G ⟶ G') {X Y : total F G} (f : X ⟶ Y) :
    HEq (leftMap ((coefficientMap α β).map f))
      ((α.app (op (base F G X))).toFunctor.map (leftMap f)) := by
  exact unop_catEqToHom_app_comp_heq _ _ _

lemma coefficientMap_rightMap_heq (α : F ⟶ F') (β : G ⟶ G') {X Y : total F G} (f : X ⟶ Y) :
    HEq (rightMap ((coefficientMap α β).map f))
      ((β.app (base F G Y)).toFunctor.map (rightMap f)) := by
  exact catEqToHom_app_comp_heq _ _ _

end SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck

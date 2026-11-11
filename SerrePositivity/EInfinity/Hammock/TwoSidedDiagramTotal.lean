module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram
public import SerrePositivity.EInfinity.Hammock.TwoSidedThomasonTransition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckCoefficientComponents

/-!
# 元の二方向図式から元の全圏への関手

概要：底と両係数の元の各射は全圏の関手を与え、恒等・合成に厳密に両立する。
方針：底・左・右の三成分で射を比較し、元の係数射の端点移送を回収する。
規約：既存の coefficientMap と baseChange の合成そのものを使う。
使われ方：DK10.2の元の単体的 Grothendieck 全圏。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
open CategoryTheory Opposite

lemma map_catEqToHom_app_comp_heq {C D : Cat.{u, u}} {H K : C ⟶ D} (h : H = K)
    (A : C) {B : D} (f : K.toFunctor.obj A ⟶ B)
    {E : Type u} [Category.{u} E] (J : D ⥤ E) :
    HEq (J.map ((eqToHom h).toNatTrans.app A ≫ f)) (J.map f) := by
  cases h
  simp

lemma map_unop_catEqToHom_app_comp_heq {C : Cat.{u, u}} {D : Type u} [Category.{u} D]
    {H K : C ⟶ Cat.of Dᵒᵖ} (h : H = K) (A : C) {B : Dᵒᵖ}
    (f : K.toFunctor.obj A ⟶ B) {E : Type u} [Category.{u} E] (J : D ⥤ E) :
    HEq (J.map (((eqToHom h).toNatTrans.app A ≫ f).unop)) (J.map f.unop) := by
  cases h
  simp

def totalFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} ⥤ Cat.{u, u} where
  obj A := Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total A.left A.right)
  map f := (TwoSidedThomason.transitionTotal f.base f.left f.right).toCatHom
  map_id A := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq _ _ rfl ?_ ?_
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_leftMap_heq (𝟙 A.left) (𝟙 A.right) f)
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_rightMap_heq (𝟙 A.left) (𝟙 A.right) f)
  map_comp f g := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro X Y h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq _ _ rfl ?_ ?_
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_leftMap_heq
        (f.left ≫ Functor.whiskerLeft f.base.op g.left)
        (f.right ≫ Functor.whiskerLeft f.base g.right) h).trans
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_leftMap_heq g.left g.right
            ((TwoSidedThomason.transitionTotal f.base f.left f.right).map h)).trans
              (map_unop_catEqToHom_app_comp_heq _ _ _ _)).symm
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_rightMap_heq
        (f.left ≫ Functor.whiskerLeft f.base.op g.left)
        (f.right ≫ Functor.whiskerLeft f.base g.right) h).trans
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_rightMap_heq g.left g.right
            ((TwoSidedThomason.transitionTotal f.base f.left f.right).map h)).trans
              (map_catEqToHom_app_comp_heq _ _ _ _)).symm

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram

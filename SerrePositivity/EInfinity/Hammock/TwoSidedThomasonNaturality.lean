module

public import SerrePositivity.EInfinity.Hammock.TwoSidedThomasonNerveMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckCoefficientComponents

/-!
# 元の二方向 nerve 比較の両係数への自然性

概要：元の bar と全圏の二つの係数射について、元の比較射の正方形は厳密に可換。
方針：同じ全射の三成分を比較し、左右の端点移送を異種等式で相殺する。
規約：元の係数自然変換・元の単体・元の比較射を保持する。
使われ方：DK9.5の比較とそのホモトピー不変性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedThomason
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W]
  {F F' : Wᵒᵖ ⥤ Cat.{u, u}} {G G' : W ⥤ Cat.{u, u}}

lemma simplex_naturality (α : F ⟶ F') (β : G ⟶ G') {n : ℕ}
    (e : ComposableArrows (labels F G n) n) :
    simplex F G e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.coefficientMap α β =
      simplex F' G' (e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map
        (((flipFunctor _ _ _).map (Functor.whiskerRight α nerveFunctor)).app
          (op (SimplexCategory.mk n)))
        (((flipFunctor _ _ _).map (Functor.whiskerRight β nerveFunctor)).app
          (op (SimplexCategory.mk n)))) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq _ _ rfl ?_ ?_
  · refine (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_leftMap_heq α β (arrow F G e h)).trans ?_
    change HEq ((α.app (op (e.obj i).base)).toFunctor.map (leftArrow F G e h))
      (leftArrow F' G' _ h)
    unfold leftArrow ContravariantThomason.leftArrow
    simp only [Functor.map_comp, eqToHom_map, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
    rfl
  · refine (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_rightMap_heq α β (arrow F G e h)).trans ?_
    change HEq ((β.app (e.obj j).base).toFunctor.map (rightArrow F G e h))
      (rightArrow F' G' _ h)
    unfold rightArrow
    simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    rfl

lemma map_naturality (α : F ⟶ F') (β : G ⟶ G') :
    map F G ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.coefficientMap α β) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.map (Functor.whiskerRight α nerveFunctor) (Functor.whiskerRight β nerveFunctor) ≫
        map F' G' := by
  ext n e
  exact simplex_naturality α β e

end SerrePositivity.EInfinity.Hammock.TwoSidedThomason

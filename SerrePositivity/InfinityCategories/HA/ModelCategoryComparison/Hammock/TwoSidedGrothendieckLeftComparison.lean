module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckDuality
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieckRightWeak

/-!
# 元の左係数比較と左右交換の可換式

概要：元の左係数比較を左右交換後の元の右係数比較と照合する。
方針：同じ二段の Grothendieck の map・pre の全成分を評価する。
規約：元の係数自然変換の自然性と全射の移送を保持する。
使われ方：DK §9.6の左係数の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck
open _root_.CategoryTheory _root_.Opposite

variable {W : Type u} [Category.{u} W] {F F' : Wᵒᵖ ⥤ Cat.{u, u}}
  (G : W ⥤ Cat.{u, u})

def leftCoefficientMap (α : F ⟶ F') : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F' G :=
  Grothendieck.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F' ⋙ G) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantMap α)

lemma leftCoefficientMap_projection (α : F ⟶ F') :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.leftCoefficientMap G α ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.projection = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.projection := rfl

lemma coefficientMap_factorization {G' : W ⥤ Cat.{u, u}} (α : F ⟶ F') (β : G ⟶ G') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.coefficientMap α β = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.rightCoefficientMap F β ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.leftCoefficientMap G' α := rfl

lemma leftCoefficientMap_dualFunctor (α : F ⟶ F') :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.leftCoefficientMap G α ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.dualFunctor F' G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.dualFunctor F G ⋙
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.rightCoefficientMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.dualLeft G) (Functor.whiskerRight α Cat.opFunctor)).op := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Quiver.Hom.unop_inj
  refine Grothendieck.ext _ _ ?_ ?_
  · apply Quiver.Hom.unop_inj
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simp [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.leftCoefficientMap, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.rightCoefficientMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.dualFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.dualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap]
      rfl
  · simp [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.leftCoefficientMap, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.rightCoefficientMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.dualFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.dualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap]
    rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck

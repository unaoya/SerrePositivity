module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.GrothendieckPointwiseWeak

/-!
# 二方向の Grothendieck 構成の右係数の不変性

概要：右係数の成分ごとの nerve 弱同値から元の全圏の同じ比較関手の弱同値性を得る。
方針：反変側の全圏上に元の右係数自然変換を制限し、Thomason 不変性を適用する。
規約：左係数と底の遷移に追加の不変性を仮定しない。
使われ方：DK §9.6・§10.4への片側の基本比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u})
  {G G' : W ⥤ Cat.{u, u}}

def rightCoefficientMap (β : G ⟶ G') : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G' :=
  Grothendieck.map (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F) β)

lemma rightCoefficientMap_projection (β : G ⟶ G') :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.rightCoefficientMap F β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.projection = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.projection := rfl

lemma rightCoefficientMap_isWeakHomotopyEquivalence (β : G ⟶ G')
    (hβ : ∀ w, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (β.app w).toFunctor)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck.rightCoefficientMap F β)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.grothendieck_map_isWeakHomotopyEquivalence
    (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F) β)
    (fun X => hβ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F).obj X))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedGrothendieck

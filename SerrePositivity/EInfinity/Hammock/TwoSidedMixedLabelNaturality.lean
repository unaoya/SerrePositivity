module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel
public import SerrePositivity.EInfinity.Hammock.NerveWeakTransport

/-!
# 元の混合全圏の対応の右集合ラベルへの自然性

概要：混合全圏と反対全圏の同じ対応は右ラベルの自然変換に厳密に両立する。
方針：元の右ラベルの要素圏の関手を反対全圏の底の変更へ送る。
規約：元の反変全圏への射影と元の右ラベルを保持する。
使われ方：右ラベルの単体次数を戻す対角の弱比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedMixedLabel
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u}) {S T : W ⥤ Type u}

def pulledMap (β : S ⟶ T) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledTotal F S ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledTotal F T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantBaseChange β.mapElements ((Functor.Elements.π T).op ⋙ F)

lemma toMixed_projection (S : W ⥤ Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.toMixed F S ⋙ Functor.Elements.π (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F ⋙ S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantBaseChange (Functor.Elements.π S) F := rfl

lemma pulledMap_projection (β : S ⟶ T) :
    pulledMap F β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantBaseChange (Functor.Elements.π T) F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantBaseChange (Functor.Elements.π S) F := rfl

lemma toMixed_naturality (β : S ⟶ T) :
    pulledMap F β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.toMixed F T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.toMixed F S ⋙ (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F) β).mapElements := rfl

lemma toMixed_nerveMap_isWeakHomotopyEquivalence (S : W ⥤ Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.toMixed F S)) :=
  nerveMap_equivalence_isWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.equivalence F S)

end SerrePositivity.EInfinity.Hammock.TwoSidedMixedLabel

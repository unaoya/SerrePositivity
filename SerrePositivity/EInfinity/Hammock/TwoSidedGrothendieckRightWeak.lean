module

public import SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieckFunctoriality
public import SerrePositivity.EInfinity.Hammock.GrothendieckPointwiseWeak

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
namespace SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck
open CategoryTheory SerrePositivity.InfinityCategories

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u})
  {G G' : W ⥤ Cat.{u, u}}

def rightCoefficientMap (β : G ⟶ G') : total F G ⥤ total F G' :=
  Grothendieck.map (Functor.whiskerLeft (contravariantProjection F) β)

lemma rightCoefficientMap_projection (β : G ⟶ G') :
    rightCoefficientMap F β ⋙ projection = projection := rfl

lemma rightCoefficientMap_isWeakHomotopyEquivalence (β : G ⟶ G')
    (hβ : ∀ w, IsWeakHomotopyEquivalence (nerveMap (β.app w).toFunctor)) :
    IsWeakHomotopyEquivalence (nerveMap (rightCoefficientMap F β)) :=
  grothendieck_map_isWeakHomotopyEquivalence
    (Functor.whiskerLeft (contravariantProjection F) β)
    (fun X => hβ ((contravariantProjection F).obj X))

end SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck

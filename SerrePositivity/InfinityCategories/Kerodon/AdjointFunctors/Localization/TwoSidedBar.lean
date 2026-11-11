module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChainNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DoubleSimplicialDiagonal
public import Mathlib.CategoryTheory.Products.Basic

/-!
# 元の二方向の要素圏による二方向 bar

概要：反変・共変の単体集合値図式から元の二重単体的 bar とその対角を構成する。
方針：各ラベル次数の二方向の要素圏の nerve を取り、同じ対角関手を適用する。
規約：全作用素・元の係数自然変換を保持する。
使われ方：DK §9.5・10.6の二方向 Grothendieck 比較への始域。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ SSet.{u}) (G : W ⥤ SSet.{u})

def rows : SimplicialObject SSet.{u} :=
  F.flip.prod' G.flip ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.elementsFunctor ⋙ nerveFunctor

def space : SSet.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (rows F G)

variable {F G} {F' : Wᵒᵖ ⥤ SSet.{u}} {G' : W ⥤ SSet.{u}}

def rowMap (α : F ⟶ F') (β : G ⟶ G') : rows F G ⟶ rows F' G' :=
  Functor.whiskerRight
    (((flipFunctor _ _ _).map α).prod' ((flipFunctor _ _ _).map β))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.elementsFunctor ⋙ nerveFunctor)

def map (α : F ⟶ F') (β : G ⟶ G') : space F G ⟶ space F' G' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (rowMap α β)

lemma rowMap_app (α : F ⟶ F') (β : G ⟶ G') (n : SimplexCategoryᵒᵖ) :
    (rowMap α β).app n = nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map
      (((flipFunctor _ _ _).map α).app n) (((flipFunctor _ _ _).map β).app n)) := rfl

lemma rowMap_id : rowMap (𝟙 F) (𝟙 G) = 𝟙 (rows F G) := by ext n e; rfl

lemma rowMap_comp {F'' : Wᵒᵖ ⥤ SSet.{u}} {G'' : W ⥤ SSet.{u}}
    (α : F ⟶ F') (β : G ⟶ G') (α' : F' ⟶ F'') (β' : G' ⟶ G'') :
    rowMap (α ≫ α') (β ≫ β') = rowMap α β ≫ rowMap α' β' := by ext n e; rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar

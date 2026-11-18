module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomasonSimplex

/-!
# 元の二方向 bar から元の Grothendieck nerve への単体的比較

概要：元の二方向 bar の対角を元の全圏の nerve へ送る実際の単体写像を構成する。
方針：各単体の比較の全作用素での交換をそのまま使う。
規約：元の底・両ラベルの対角頂点・全射を保持する。弱同値性は後続。
使われ方：DK9.5の元の比較射。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason
open _root_.CategoryTheory _root_.Opposite

variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

def map : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space (F ⋙ nerveFunctor) (G ⋙ nerveFunctor) ⟶ nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G) where
  app _ := ↾fun e => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.simplex F G e
  naturality {n m} θ := by
    ext e
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.simplex_operator F G e θ.unop

lemma map_vertex (n : ℕ) (e : ComposableArrows (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.labels F G n) n) (i : Fin (n + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.map F G).app (op (SimplexCategory.mk n)) e).obj i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk F G (e.obj i).base ((e.obj i).left.obj i) ((e.obj i).right.obj i) := rfl

lemma map_projection (n : ℕ) (e : ComposableArrows (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.labels F G n) n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.map F G).app (op (SimplexCategory.mk n)) e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.projection =
      e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.projection _ _ := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason

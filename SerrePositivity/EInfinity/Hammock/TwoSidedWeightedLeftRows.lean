module

public import SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftMap
public import SerrePositivity.EInfinity.FrameHom.ThomasonNerveMap

/-!
# 元の右ラベル次数を動かす重み付き左比較

概要：右ラベルの各次数の元の左比較を、元の一方向 bar への二重単体的比較へ束ねる。
方針：右ラベルの射への厳密な自然性を同じ図式の作用素に使う。
規約：元の両ラベルと全作用素を保持し、行の弱同値性は仮定しない。
使われ方：DK9.5の行ごとの弱比較を元の対角射へ戻す準備。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeft
open CategoryTheory Opposite
open SerrePositivity.SimplicialModel

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u})

def spaces : (W ⥤ Type u) ⥤ SSet.{u} where
  obj S := space F S
  map β := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.map (𝟙 (F ⋙ nerveFunctor))
    (Functor.whiskerRight β (Functor.const SimplexCategoryᵒᵖ))
  map_id S := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap (𝟙 _) (𝟙 _)) = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap_id, CategoryTheory.Functor.map_id]
  map_comp β γ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap ((𝟙 (F ⋙ nerveFunctor)) ≫ 𝟙 _)
        ((Functor.whiskerRight β (Functor.const SimplexCategoryᵒᵖ)) ≫
          Functor.whiskerRight γ (Functor.const SimplexCategoryᵒᵖ))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap_comp, CategoryTheory.Functor.map_comp]
    rfl

def rows (G : W ⥤ Cat.{u, u}) : SimplicialObject SSet.{u} :=
  (G ⋙ nerveFunctor).flip ⋙ spaces F

def rowMap (G : W ⥤ Cat.{u, u}) : rows F G ⟶
    (BarConstruction.rows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F)).obj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F ⋙ G) ⋙ nerveFunctor) where
  app n := map F ((G ⋙ nerveFunctor).flip.obj n)
  naturality {n _} θ := (map_labels F ((G ⋙ nerveFunctor).flip.obj n)
    ((G ⋙ nerveFunctor).flip.map θ)).symm

def diagonalSourceIso (G : W ⥤ Cat.{u, u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (rows F G) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space (F ⋙ nerveFunctor) (G ⋙ nerveFunctor) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro e
    rfl)

def diagonalMap (G : W ⥤ Cat.{u, u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space (F ⋙ nerveFunctor) (G ⋙ nerveFunctor) ⟶
      (BarConstruction.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F)).obj
        (FrameHom.Thomason.nerveDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F ⋙ G)) :=
  (diagonalSourceIso F G).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (rowMap F G)

end SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeft

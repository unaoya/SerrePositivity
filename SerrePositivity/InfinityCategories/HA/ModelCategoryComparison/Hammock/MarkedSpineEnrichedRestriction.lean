module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineEnrichedFoldUnique
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineMarkedComposition

/-!
# 元の全因子列からの豊穣関手の二つの生成部分への制限

概要：任意の豊穣関手から元の指定因子と非指定生成矢の像を回収する。
方針：元の包含の合成・単位保存と元の豊穣関手の公理を使う。
規約：対象写像を同じ元の写像に保持する。
使われ方：自由積の普遍的な拡張と制限の両逆。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {D : Type uD} [EnrichedCategory SSet.{u} D]

def restrictEnrichedFunctor :
    letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.enrichedCategory W
    EnrichedFunctor SSet.{u} (Paths C) D → _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D := by
  letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.enrichedCategory W
  intro G
  exact
    { obj := G.obj
      marked := fun X Y => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.nilMap W Y X ≫ G.map X Y
      generator := fun g => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.generatorMap W g ≫ G.map g.val.left g.val.right
      marked_unit := fun X => by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.marked_unitMap]
        exact G.map_id X
      marked_comp := fun X Y Z => by
        have hc : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.composition W X Y Z ≫ G.map X Z =
            (G.map X Y ⊗ₘ G.map Y Z) ≫ eComp SSet.{u} (G.obj X) (G.obj Y) (G.obj Z) :=
          G.map_comp X Y Z
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.marked_composition, Category.assoc]
        change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.nilMap W Y X ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.nilMap W Z Y) ≫
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.composition W X Y Z ≫ G.map X Z) = _
        rw [hc]
        rw [← Category.assoc, tensorHom_comp_tensorHom] }

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

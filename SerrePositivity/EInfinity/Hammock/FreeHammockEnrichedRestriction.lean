module

public import SerrePositivity.EInfinity.Hammock.FreeHammockEnrichedFoldUnique
public import SerrePositivity.EInfinity.Hammock.AllMarkedEnrichedInclusion
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory

/-!
# 元の自由圏の hammock の豊穣拡張と二つの生成部分への制限

概要：元の hammock 自身の豊穣関手へ拡張し、逆に二つの元の生成部分へ制限する。
方針：元の単位・合成保存と包含の保存を豊穣関手の公理へ渡す。
規約：元の全語の余極限による豊穣圏を使う。
使われ方：DK 命題3.2の元の自由積の豊穣普遍性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {D : Type uD} [EnrichedCategory SSet.{u} D]

def EnrichedFoldData.hammockEnrichedFunctor (F : EnrichedFoldData W D) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    EnrichedFunctor SSet.{u} (Paths C) D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  exact
    { obj := F.obj
      map := F.hammockFoldMap
      map_id := F.hammockFoldMap_unit
      map_comp := F.hammockFoldMap_comp }

def restrictHammockEnrichedFunctor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    EnrichedFunctor SSet.{u} (Paths C) D → EnrichedFoldData W D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  intro G
  exact
    { obj := G.obj
      marked := fun X Y => AllMarked.inclusion W X Y ≫ G.map X Y
      generator := fun g => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W.paths g.val.hom.toPath ≫ G.map g.val.left g.val.right
      marked_unit := fun X => by
        rw [← Category.assoc, AllMarked.inclusion_unit]
        exact G.map_id X
      marked_comp := fun X Y Z => by
        have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W.paths X Y Z ≫ G.map X Z =
            (G.map X Y ⊗ₘ G.map Y Z) ≫ eComp SSet.{u} (G.obj X) (G.obj Y) (G.obj Z) :=
          G.map_comp X Y Z
        rw [← Category.assoc, AllMarked.inclusion_composition, Category.assoc, hc,
          ← Category.assoc, tensorHom_comp_tensorHom] }

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

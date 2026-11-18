module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeHammockEnrichedRestriction
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineEnrichedUniversal

/-!
# 元の自由圏の hammock の豊穣自由積の普遍性

概要：任意の豊穣目標への元の hammock からの関手は二つの生成部分の像と同値である。
方針：元の単体写像の一意性により拡張と制限が互いに逆であることを証明する。
規約：元の全語の余極限・対象写像・元の豊穣合成を保持する。
使われ方：DK 命題3.2による元の自由圏の hammock の自由積分解。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D]

lemma restrict_hammock_extend (F : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictHammockEnrichedFunctor W (F.hammockEnrichedFunctor W) = F := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData.ext
    (F := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictHammockEnrichedFunctor W (F.hammockEnrichedFunctor W)) (G := F) rfl
  · exact heq_of_eq (funext fun X => funext fun Y => F.hammockFoldMap_marked X Y)
  · exact heq_of_eq (funext fun g => F.hammockFoldMap_generator g)

lemma extend_hammock_restrict :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    ∀ G : EnrichedFunctor SSet.{u} (Paths C) D,
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictHammockEnrichedFunctor W G).hammockEnrichedFunctor W = G := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  intro G
  apply EnrichedFunctor.ext SSet.{u}
    (F := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictHammockEnrichedFunctor W G).hammockEnrichedFunctor W) (G := G) (fun _ => rfl)
  intro X Y
  have he := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictHammockEnrichedFunctor W G).hammockFoldMap_unique G.map (fun _ _ => rfl)
    (fun _ => rfl) (fun X Y Z => G.map_comp X Y Z) X Y
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictHammockEnrichedFunctor W G).hammockFoldMap X Y ≫
    𝟙 (G.obj X ⟶[SSet.{u}] G.obj Y) = G.map X Y
  exact (Category.comp_id ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictHammockEnrichedFunctor W G).hammockFoldMap X Y)).trans he.symm

def hammockEnrichedFunctorEquiv (W : MorphismProperty C) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    EnrichedFunctor SSet.{u} (Paths C) D ≃ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  exact
    { toFun := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictHammockEnrichedFunctor W
      invFun := fun F => F.hammockEnrichedFunctor W
      left_inv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.extend_hammock_restrict
      right_inv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrict_hammock_extend }

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

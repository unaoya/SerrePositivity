module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeHammockEnrichedFreeProduct

/-!
# 元の豊穣自由積の二つの包含上の回収と外延性

概要：元の拡張を二つの包含で制限すると指定した元の関手を回収する。
方針：元の関手の組の回収式と同じ全単射の単射性を使う。
規約：元の対象写像と全 Hom の単体写像を回収する。
使われ方：DK 命題3.2の自由積分解の二つの脚と一意性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {D : Type uD} [EnrichedCategory SSet.{u} D]

lemma freeProductExtension_marked (P : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts W D) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.markedInclusionFunctor W).comp SSet.{u} (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.freeProductExtension W P) = P.marked := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  exact congrArg _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts.marked (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.freeProductExtension_fac W P)

lemma freeProductExtension_unmarked (P : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts W D) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
      (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unmarkedInclusionFunctor W).comp SSet.{u} (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.freeProductExtension W P) = P.unmarked := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
    (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  exact congrArg _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts.unmarked (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.freeProductExtension_fac W P)

lemma freeProduct_hom_ext :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
      (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    ∀ F G : EnrichedFunctor SSet.{u} (Paths C) D,
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.markedInclusionFunctor W).comp SSet.{u} F = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.markedInclusionFunctor W).comp SSet.{u} G →
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unmarkedInclusionFunctor W).comp SSet.{u} F = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unmarkedInclusionFunctor W).comp SSet.{u} G →
      F = G := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
    (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  intro F G hm hu
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.freeProductFunctorEquiv W).injective (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts.ext hm hu)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

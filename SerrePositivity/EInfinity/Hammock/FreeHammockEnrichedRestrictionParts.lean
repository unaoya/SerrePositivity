module

public import SerrePositivity.EInfinity.Hammock.FreeHammockEnrichedInclusions

/-!
# 元の自由積の制限と二つの元の豊穣包含との合成

概要：普遍性の制限の二成分を元の二つの包含との合成へ照合する。
方針：指定部分は元の全 Hom、非指定部分は元の自由圏の生成矢で照合する。
規約：同じ元の包含と対象表示を保持する。
使われ方：元の自由積の包含を指定した豊穣普遍性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {D : Type uD} [EnrichedCategory SSet.{u} D]

lemma restrict_marked_comp :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    ∀ G : EnrichedFunctor SSet.{u} (Paths C) D,
      (restrictHammockEnrichedFunctor W G).parts.marked =
        (markedInclusionFunctor W).comp SSet.{u} G := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  intro G
  rfl

lemma restrict_unmarked_comp :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
      (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    ∀ G : EnrichedFunctor SSet.{u} (Paths C) D,
      (restrictHammockEnrichedFunctor W G).parts.unmarked =
        (unmarkedInclusionFunctor W).comp SSet.{u} G := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
    (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  intro G
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment.functorEquiv.injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment.functorEquiv
      (restrictHammockEnrichedFunctor W G).unmarkedEnrichedFunctor =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment.functorEquiv ((unmarkedInclusionFunctor W).comp SSet.{u} G)
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment.functorEquiv
      (restrictHammockEnrichedFunctor W G).unmarkedEnrichedFunctor =
        (restrictHammockEnrichedFunctor W G).unmarkedPrefunctor :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment.functorEquiv.apply_symm_apply _
  rw [hl]
  apply Prefunctor.ext (F := (restrictHammockEnrichedFunctor W G).unmarkedPrefunctor)
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment.functorEquiv ((unmarkedInclusionFunctor W).comp SSet.{u} G))
    (fun _ => rfl)
  intro X Y f
  have hg := unmarkedInclusion_generator W (⟨⟨X, Y, f.val⟩, f.property⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
  change ForgetEnrichment.homOf SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W.paths f.val.toPath ≫ G.map X Y) =
    ForgetEnrichment.homOf SSet.{u}
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point f.toPath ≫ (unmarkedInclusionFunctor W).map X Y) ≫ G.map X Y)
  exact congrArg (fun k => ForgetEnrichment.homOf SSet.{u} (k ≫ G.map X Y)) hg.symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

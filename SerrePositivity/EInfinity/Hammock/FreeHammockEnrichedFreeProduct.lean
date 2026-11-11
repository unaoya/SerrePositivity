module

public import SerrePositivity.EInfinity.Hammock.FreeHammockEnrichedRestrictionParts

/-!
# 元の二つの包含を指定した自由圏の hammock の豊穣自由積

概要：元の指定 hammock と非指定自由部分からの関手は一意に元の hammock へ拡張する。
方針：元の二つの包含との合成による制限を既存の全単射へ照合する。
規約：共通対象の等式と元の全 Hom の単体写像を保持する。
使われ方：DK 命題3.2の自由積分解と全指定自由圏への帰着。
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

def restrictParts :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    EnrichedFunctor SSet.{u} (Paths C) D → EnrichedParts W D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
    (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  intro G
  exact
    { marked := (markedInclusionFunctor W).comp SSet.{u} G
      unmarked := (unmarkedInclusionFunctor W).comp SSet.{u} G
      objects _ := rfl }

lemma restrictParts_eq :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    ∀ G : EnrichedFunctor SSet.{u} (Paths C) D,
      restrictParts W G = (restrictHammockEnrichedFunctor W G).parts := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  intro G
  apply EnrichedParts.ext
  · exact (restrict_marked_comp W G).symm
  · exact (restrict_unmarked_comp W G).symm

def freeProductFunctorEquiv :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    EnrichedFunctor SSet.{u} (Paths C) D ≃ EnrichedParts W D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  let e := freeProductEnrichedFunctorEquiv (D := D) W
  exact
    { toFun := restrictParts W
      invFun := e.symm
      left_inv := fun G => (congrArg e.symm (restrictParts_eq W G)).trans (e.symm_apply_apply G)
      right_inv := fun P => (restrictParts_eq W (e.symm P)).trans (e.apply_symm_apply P) }

def freeProductExtension (P : EnrichedParts W D) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    EnrichedFunctor SSet.{u} (Paths C) D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  exact (freeProductFunctorEquiv W).symm P

lemma freeProductExtension_fac (P : EnrichedParts W D) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    restrictParts W (freeProductExtension W P) = P := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  exact (freeProductFunctorEquiv W).apply_symm_apply P

lemma existsUnique_freeProductExtension (P : EnrichedParts W D) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    ∃! G : EnrichedFunctor SSet.{u} (Paths C) D, restrictParts W G = P := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  refine ⟨freeProductExtension W P, freeProductExtension_fac W P, ?_⟩
  intro G hG
  exact (freeProductFunctorEquiv W).injective (hG.trans (freeProductExtension_fac W P).symm)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

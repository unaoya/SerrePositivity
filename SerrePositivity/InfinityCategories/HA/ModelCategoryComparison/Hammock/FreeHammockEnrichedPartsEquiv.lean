module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeHammockEnrichedPartsRecovery

/-!
# 元の二つの部分からの豊穣関手と生成矢の像の指定の同値

概要：共通対象の表示の等式を含む二つの関手の組を元の生成表示へ同定する。
方針：元の自由圏の普遍性と対象等式に沿う Hom の移送を使う。
規約：全対象写像・全 Hom の単体写像を回収する。
使われ方：元の自由圏の hammock の自由積の豊穣普遍性。
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

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts.ext {F G : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts W D} (hm : F.marked = G.marked)
    (hu : F.unmarked = G.unmarked) : F = G := by
  cases F
  cases G
  cases hm
  cases hu
  rfl

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts.foldData_parts (G : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts W D) : G.foldData.parts = G := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
    (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts.ext (F := G.foldData.parts) (G := G)
  · apply EnrichedFunctor.ext SSet.{u} (F := G.foldData.markedEnrichedFunctor)
      (G := G.marked) (fun _ => rfl)
    intro X Y
    change G.marked.map X Y ≫ 𝟙 _ = G.marked.map X Y
    exact Category.comp_id _
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment.functorEquiv.symm G.foldData.unmarkedPrefunctor = G.unmarked
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment.functorEquiv.symm G.foldData_prefunctor).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment.functorEquiv.symm_apply_apply G.unmarked)

def enrichedPartsEquiv : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D ≃ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts W D where
  toFun := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData.parts
  invFun := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts.foldData
  left_inv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData.parts_foldData
  right_inv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts.foldData_parts

def freeProductEnrichedFunctorEquiv (W : MorphismProperty C) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
    EnrichedFunctor SSet.{u} (Paths C) D ≃ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedParts W D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory W.paths
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.hammockEnrichedFunctorEquiv W).trans _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.enrichedPartsEquiv

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

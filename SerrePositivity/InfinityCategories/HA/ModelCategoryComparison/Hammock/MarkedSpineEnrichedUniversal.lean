module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineEnrichedRestriction

/-!
# 元の指定因子と非指定生成矢による豊穣関手の普遍性

概要：任意の豊穣目標への拡張と元の二つの生成部分への制限は互いに逆である。
方針：元の単体写像の一意性と全関手の外延性を使う。
規約：対象写像と元の全 Hom の単体写像を保持する。
使われ方：自由積の豊穣普遍性の全単射。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D]

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData.ext {F G : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D} (ho : F.obj = G.obj)
    (hm : HEq F.marked G.marked) (hg : HEq F.generator G.generator) : F = G := by
  cases F
  cases G
  cases ho
  cases eq_of_heq hm
  cases eq_of_heq hg
  rfl

lemma restrict_extend (F : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictEnrichedFunctor W F.enrichedFunctor = F := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData.ext (F := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictEnrichedFunctor W F.enrichedFunctor) (G := F) rfl
  · exact heq_of_eq (funext fun X => funext fun Y => F.foldMap_marked X Y)
  · exact heq_of_eq (funext fun g => F.foldMap_generator g)

lemma extend_restrict :
    letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.enrichedCategory W
    ∀ G : EnrichedFunctor SSet.{u} (Paths C) D,
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictEnrichedFunctor W G).enrichedFunctor = G := by
  let := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.enrichedCategory W
  intro G
  apply EnrichedFunctor.ext SSet.{u} (F := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictEnrichedFunctor W G).enrichedFunctor)
    (G := G) (fun _ => rfl)
  intro X Y
  have he := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictEnrichedFunctor W G).foldMap_unique G.map (fun _ _ => rfl)
    (fun _ => rfl) (fun X Y Z => G.map_comp X Y Z) X Y
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictEnrichedFunctor W G).foldMap X Y ≫
    𝟙 (G.obj X ⟶[SSet.{u}] G.obj Y) = G.map X Y
  exact (Category.comp_id ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictEnrichedFunctor W G).foldMap X Y)).trans he.symm

def enrichedFunctorEquiv (W : MorphismProperty C) :
    letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.enrichedCategory W
    EnrichedFunctor SSet.{u} (Paths C) D ≃ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D := by
  letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.enrichedCategory W
  exact
    { toFun := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrictEnrichedFunctor W
      invFun := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData.enrichedFunctor
      left_inv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.extend_restrict
      right_inv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.restrict_extend }

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

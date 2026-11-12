module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFreeEnrichedFunctor

/-!
# 元の指定 hammock と非指定自由部分からの豊穣関手の組

概要：自由積の二つの元の部分からの関手と対象表示の等式を記録する。
方針：元の指定部分と非指定自由部分のそれぞれの豊穣構造を使う。
規約：共通対象の表示の等式を保持する。
使われ方：元の生成矢の像による普遍性との同値。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C]

structure EnrichedParts (W : MorphismProperty C) (D : Type uD)
    [EnrichedCategory SSet.{u} D] where
  marked :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
    EnrichedFunctor SSet.{u} (WideSubcategory W.paths) D
  unmarked :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
      (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
    EnrichedFunctor SSet.{u} (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W))) D
  objects :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
      (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
    ∀ X : C, marked.obj (⟨X⟩ : WideSubcategory W.paths) = unmarked.obj X

namespace EnrichedFoldData
variable {W : MorphismProperty C} {D : Type uD} [EnrichedCategory SSet.{u} D]
  (F : EnrichedFoldData W D)

def markedEnrichedFunctor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
    EnrichedFunctor SSet.{u} (WideSubcategory W.paths) D := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  exact
    { obj := fun X => F.obj X.obj
      map := fun X Y => F.marked X.obj Y.obj
      map_id := fun X => F.marked_unit X.obj
      map_comp := fun X Y Z => F.marked_comp X.obj Y.obj Z.obj }

def parts : EnrichedParts W D where
  marked := F.markedEnrichedFunctor
  unmarked := F.unmarkedEnrichedFunctor
  objects _ := rfl

end EnrichedFoldData
end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

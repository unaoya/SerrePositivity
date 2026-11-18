module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AllMarkedNative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit

/-!
# 指定部分圏の包含と元の端点等式の移送

概要：実際の二つの hammock の端点移送は元の包含と可換である。
方針：元の端点の等式を消去し恒等移送を回収する。
規約：指定部分圏の元の包含を変更しない。
使われ方：ambient の点の回収を指定部分圏の点へ反映する。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {X X' Y Y' : Paths C}

lemma inclusion_endpoint (hX : X = X') (hY : Y = Y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap (⊤ : MorphismProperty (WideSubcategory W.paths))
      (congrArg (fun Z : Paths C => (⟨Z⟩ : WideSubcategory W.paths)) hX)
      (congrArg (fun Z : Paths C => (⟨Z⟩ : WideSubcategory W.paths)) hY) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X' Y' =
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimit.colimitMap W.paths hX hY := by
  cases hX
  cases hY
  change 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y =
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y ≫ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y)
  rw [Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked

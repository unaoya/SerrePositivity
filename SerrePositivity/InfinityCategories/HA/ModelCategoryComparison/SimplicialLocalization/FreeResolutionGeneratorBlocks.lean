module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionGeneratorPartition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockCategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockParts

/-!
# 元の自由解像の全次数の交互標準形

概要：元の各自由次数の射と圏を、指定・非指定の生成矢の交互標準形へ同定する。
方針：元の最外層の生成圏に正規化の全単射と圏同値を代入する。
規約：元の全対象・射列・合成・恒等文字を保持する。hammock の弱比較は後続。
使われ方：元の自由解像の各 hammock の行の分解。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory

def freeResolutionBlockEquiv (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X Y : ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).category) :
    (X ⟶ Y) ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockEquivalence.equivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences X Y

def freeResolutionBlockCategoryEquivalence (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockCategory.BlockCategory (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences ≌
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).category :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockCategory.categoryEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences

lemma freeResolutionBlockEquiv_symm_apply (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X Y : ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).category)
    (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences X Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionBlockEquiv C n X Y).symm N =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences N := rfl

lemma freeResolutionBlockEquiv_id (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X : ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionBlockEquiv C n X X (𝟙 X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences X := rfl

lemma freeResolutionBlockEquiv_comp (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    {X Y Z : ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).category} (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionBlockEquiv C n X Z (f ≫ g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockComposition.comp (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionBlockEquiv C n X Y f) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionBlockEquiv C n Y Z g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockComposition.normalize_comp (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences f g

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagram
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionGeneratorPartition
public import SerrePositivity.EInfinity.Hammock.UnmarkedGeneratorValue

/-!
# 元の自由 hammock の全次数の非指定生成文字列

概要：各自由次数の元の全語の余極限を、同じ次数の非指定生成文字列へ評価する。
方針：元の最外層の生成圏と既存の固定対象へ、全語に不変な評価を代入する。
規約：元の各語の標準射による回収式を保持する。次数を跨ぐ不変性は要求しない。
使われ方：Dwyer–Kan 比較補題2.3の各自由次数の hammock の分解。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory

def freeHammockGeneratorWordValue (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockResolution C X Y).obj n ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj
        (List (Quiver.Total (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).category)) :=
  _root_.SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.colimitValue (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n Y)

lemma freeHammockGeneratorWordValue_fac (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n Y) w ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockGeneratorWordValue C X Y n =
          _root_.SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.graphValue
            (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences :=
  _root_.SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.graphInclusion_colimitValue
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorBase C n).weakEquivalences _ _ w

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

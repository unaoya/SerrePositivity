module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PaddedComparisonRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph

/-!
# 元の三列の標準射と padding 余極限比較の一致

概要：三列の標準射の後の padding 比較は、anodyne 反転後に元の回収比較と一致する。
方針：両方を元の B(threeArrow) の標準射の前の二つの包含として表示する。
規約：対象は実際の元の graph 図式。元の colimit と元の標準射を保持する。
使われ方：分数計算と左逆から元の三列の包含の弱同値性を回収する。
-/

@[expose] public section
universe u v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

lemma paddedThreeComparison_as_outer {D : Type uH} [Category.{vH} D] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ D)
    [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedThreeComparison F = F.map _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap ≫
      colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedThreeComparison _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.outerWordMap
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  exact congrArg (fun g => F.map (eqToHom _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.padding_single_forward.symm) ≫ g)
    (colimit.w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.centerInclusion).symm

lemma paddingColimitMap_threeArrow {D : Type uH} [Category.{vH} D] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ D)
    [HasColimit F] [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F)] :
    colimit.ι F _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitMap F = F.map _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.innerWordMap ≫
      colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow :=
  ι_colimMap (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingInclusionNat F) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma colimit_comparison_image_eq :
    L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedThreeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)) =
      L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)) := by
  change L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedThreeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)) =
    L.map (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y))
  rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.paddedThreeComparison_as_outer, paddingColimitMap_threeArrow,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.original_maps_image_eq X Y L hL]

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

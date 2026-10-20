module

public import SerrePositivity.EInfinity.Hammock.ThreeArrowPaddingComparison
public import SerrePositivity.EInfinity.Hammock.PaddedComparisonRecovery
public import SerrePositivity.EInfinity.Hammock.ColimitGraph

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
namespace SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra FrameHom

lemma paddedThreeComparison_as_outer {D : Type uH} [Category.{vH} D] (F : Word ⥤ D)
    [HasColimit (Word.paddingFunctor ⋙ F)] :
    paddedThreeComparison F = F.map outerWordMap ≫
      colimit.ι (Word.paddingFunctor ⋙ F) Word.threeArrow := by
  unfold paddedThreeComparison outerWordMap
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  exact congrArg (fun g => F.map (eqToHom Word.padding_single_forward.symm) ≫ g)
    (colimit.w (Word.paddingFunctor ⋙ F) centerInclusion).symm

lemma paddingColimitMap_threeArrow {D : Type uH} [Category.{vH} D] (F : Word ⥤ D)
    [HasColimit F] [HasColimit (Word.paddingFunctor ⋙ F)] :
    colimit.ι F Word.threeArrow ≫ paddingColimitMap F = F.map innerWordMap ≫
      colimit.ι (Word.paddingFunctor ⋙ F) Word.threeArrow :=
  ι_colimMap (Functor.whiskerRight Word.paddingInclusionNat F) Word.threeArrow

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma colimit_comparison_image_eq :
    L.map (paddedThreeComparison (graphDiagram (weakEquivalences C) X Y)) =
      L.map (graphInclusion (weakEquivalences C) X Y Word.threeArrow ≫
        paddingColimitMap (graphDiagram (weakEquivalences C) X Y)) := by
  change L.map (paddedThreeComparison (graphDiagram (weakEquivalences C) X Y)) =
    L.map (colimit.ι (graphDiagram (weakEquivalences C) X Y) Word.threeArrow ≫
      paddingColimitMap (graphDiagram (weakEquivalences C) X Y))
  rw [paddedThreeComparison_as_outer, paddingColimitMap_threeArrow,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    original_maps_image_eq X Y L hL]

end SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding

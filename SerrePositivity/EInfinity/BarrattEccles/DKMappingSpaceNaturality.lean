module

public import SerrePositivity.EInfinity.BarrattEccles.DKHammockEndpointNaturality
public import SerrePositivity.EInfinity.BarrattEccles.DKMappingSpaceComparison
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceHammockNaturality

/-!
# 実 DK Hom と既存 Map^h の同じ高次比較の自然性

概要：元の cofibrant 代数の射による前後合成の正方形を証明する。
方針：同じ reduced hammock への元の因子化と両比較の自然性を使う。
規約：既存の比較同型・既存の Map^h・実 DK Hom の元の作用を保持する。
使われ方：Kan DK Hom の比較と既存 π₀ 比較への接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

lemma cofibrantAlgebraDKMappingSpaceComparisonIso_postcompose
    (X : (cofibrantAlgebraRelativeCategory A).category)
    {Y Z : (cofibrantAlgebraRelativeCategory A).category} (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPostcompose (cofibrantAlgebraRelativeCategory A) X g) ≫
      (cofibrantAlgebraDKMappingSpaceComparisonIso A X Z).hom =
    (cofibrantAlgebraDKMappingSpaceComparisonIso A X Y).hom ≫
      AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        (((mappingSpace A).obj (op ((cofibrantAlgebraDKInclusion A).obj X))).map
          ((cofibrantAlgebraDKInclusion A).map g))) := by
  apply (cancel_mono (mappingSpaceReducedHammockComparisonIso A
    ((cofibrantAlgebraDKInclusion A).obj X) ((cofibrantAlgebraDKInclusion A).obj Z)).hom).1
  rw [Category.assoc, cofibrantAlgebraDKMappingSpaceComparisonIso_hammock,
    Category.assoc, mappingSpaceReducedHammockComparisonIso_postcompose,
    ← Category.assoc, cofibrantAlgebraDKMappingSpaceComparisonIso_hammock,
    cofibrantAlgebraDKHammockComparisonIso_postcompose]

lemma cofibrantAlgebraDKMappingSpaceComparisonIso_precompose
    (Z : (cofibrantAlgebraRelativeCategory A).category)
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPrecompose (cofibrantAlgebraRelativeCategory A) Z f) ≫
      (cofibrantAlgebraDKMappingSpaceComparisonIso A X Z).hom =
    (cofibrantAlgebraDKMappingSpaceComparisonIso A Y Z).hom ≫
      AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        (((mappingSpace A).map ((cofibrantAlgebraDKInclusion A).map f).op).app
          ((cofibrantAlgebraDKInclusion A).obj Z))) := by
  apply (cancel_mono (mappingSpaceReducedHammockComparisonIso A
    ((cofibrantAlgebraDKInclusion A).obj X) ((cofibrantAlgebraDKInclusion A).obj Z)).hom).1
  rw [Category.assoc, cofibrantAlgebraDKMappingSpaceComparisonIso_hammock,
    Category.assoc, mappingSpaceReducedHammockComparisonIso_precompose,
    ← Category.assoc, cofibrantAlgebraDKMappingSpaceComparisonIso_hammock,
    cofibrantAlgebraDKHammockComparisonIso_precompose]

lemma cofibrantAlgebraDKMappingSpaceComparisonIso_naturality
    {X' X Y Y' : (cofibrantAlgebraRelativeCategory A).category} (f : X' ⟶ X) (g : Y ⟶ Y') :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPrecompose (cofibrantAlgebraRelativeCategory A) Y f ≫
          _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPostcompose (cofibrantAlgebraRelativeCategory A) X' g) ≫
      (cofibrantAlgebraDKMappingSpaceComparisonIso A X' Y').hom =
    (cofibrantAlgebraDKMappingSpaceComparisonIso A X Y).hom ≫
      AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        ((((mappingSpace A).map ((cofibrantAlgebraDKInclusion A).map f).op).app
            ((cofibrantAlgebraDKInclusion A).obj Y)) ≫
          (((mappingSpace A).obj (op ((cofibrantAlgebraDKInclusion A).obj X'))).map
            ((cofibrantAlgebraDKInclusion A).map g)))) := by
  rw [Functor.map_comp, Category.assoc, cofibrantAlgebraDKMappingSpaceComparisonIso_postcompose,
    ← Category.assoc, cofibrantAlgebraDKMappingSpaceComparisonIso_precompose, Category.assoc,
    Functor.map_comp, Functor.map_comp]

end SerrePositivity.EInfinity.BarrattEccles

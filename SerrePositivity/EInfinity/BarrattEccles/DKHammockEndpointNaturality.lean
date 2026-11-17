module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantHammockActions
public import SerrePositivity.EInfinity.BarrattEccles.DKHammockComparisonFactorization
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKReducedHammockEndpointNaturality

/-!
# 元の代数 DK/hammock 比較の両端点自然性

概要：実際の cofibrant 包含を通る同じ比較は元の前後合成を保つ。
方針：native DK 比較の自然性と既存包含の作用の正方形を合成する。
規約：元の比較の因子化・元の自由射・元の HomLift 同型を保持する。
使われ方：実 DK Hom と既存 Map^h の高次比較の自然性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

lemma cofibrantAlgebraDKHammockComparisonIso_postcompose
    (X : (cofibrantAlgebraRelativeCategory A).category)
    {Y Z : (cofibrantAlgebraRelativeCategory A).category} (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPostcompose (cofibrantAlgebraRelativeCategory A) X g) ≫
      (cofibrantAlgebraDKHammockComparisonIso A X Z).hom =
    (cofibrantAlgebraDKHammockComparisonIso A X Y).hom ≫
      AnodyneHomotopy.anodyneQ.map (algebraReducedHammockPostcompose A
        ((cofibrantAlgebraDKInclusion A).obj X) ((cofibrantAlgebraDKInclusion A).map g)) := by
  have h := congrArg AnodyneHomotopy.anodyneQ.map
    (cofibrantAlgebraHammockInclusionMap_postcompose A X g)
  simp only [Functor.map_comp] at h
  rw [cofibrantAlgebraDKHammockComparisonIso_factorization,
    cofibrantAlgebraDKHammockComparisonIso_factorization,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_postcompose, Category.assoc, h, ← Category.assoc]

lemma cofibrantAlgebraDKHammockComparisonIso_precompose
    (Z : (cofibrantAlgebraRelativeCategory A).category)
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPrecompose (cofibrantAlgebraRelativeCategory A) Z f) ≫
      (cofibrantAlgebraDKHammockComparisonIso A X Z).hom =
    (cofibrantAlgebraDKHammockComparisonIso A Y Z).hom ≫
      AnodyneHomotopy.anodyneQ.map (algebraReducedHammockPrecompose A
        ((cofibrantAlgebraDKInclusion A).obj Z) ((cofibrantAlgebraDKInclusion A).map f)) := by
  have h := congrArg AnodyneHomotopy.anodyneQ.map
    (cofibrantAlgebraHammockInclusionMap_precompose A Z f)
  simp only [Functor.map_comp] at h
  rw [cofibrantAlgebraDKHammockComparisonIso_factorization,
    cofibrantAlgebraDKHammockComparisonIso_factorization,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_precompose, Category.assoc, h, ← Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles

module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKHammockEndpointNaturality
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ReducedPointActions

/-!
# 元の射に沿う既存の reduced DK 比較の自然性

概要：既存の reduced 比較は元の射による前後合成を保つ。
方針：同じ正規化との因子化へ証明済みの元の余極限の自然性を移す。
規約：既存の比較同型を変更せず、元の生成射と全単体を保持する。
使われ方：実 DK Hom と既存 Map^h の比較の両端点自然性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma dkHammockComparisonIso_postcompose (X : C.category) {Y Z : C.category} (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPostcompose C X g) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Z).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPostcomposeMap C.weakEquivalences X g) := by
  have h := congrArg AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_postcompose C.weakEquivalences X g)
  simp only [Functor.map_comp] at h
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_reduction, ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_reduction,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso_postcompose, Category.assoc,
    ← h, ← Category.assoc]

lemma dkHammockComparisonIso_precompose {X Y : C.category} (Z : C.category) (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPrecompose C Z f) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Z).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C Y Z).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPrecomposeMap C.weakEquivalences Z f) := by
  have h := congrArg AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_precompose C.weakEquivalences Z f)
  simp only [Functor.map_comp] at h
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_reduction, ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_reduction,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso_precompose, Category.assoc,
    ← h, ← Category.assoc]

lemma dkHammockComparisonIso_arrow {X Y : C.category} (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint C f) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Y).hom =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedArrowMap C.weakEquivalences f) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_reduction, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockColimitComparisonIso_arrow, ← Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

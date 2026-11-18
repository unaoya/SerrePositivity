module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActions
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitArrowMap
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ReducedColimit

/-!
# 元の射による reduced hammock の前後合成

概要：既存の正規化同型で元の前後合成を同じ reduced hammock へ送る。
方針：元の余極限の合成と正規化を使う。
規約：元の全単体と元の射を保持する。
使われ方：既存の DK と Map^h の高次比較の自然性。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

def reducedArrowMap {X Y : C} (f : X ⟶ Y) : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Y).hom

def reducedPostcomposeMap (X : C) {Y Z : C} (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Z :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Y).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Z).hom

def reducedPrecomposeMap {X Y : C} (Z : C) (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W Y Z ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Z :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W Y Z).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Z ≫
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Z).hom

lemma reducedColimitIso_postcompose (X : C) {Y Z : C} (g : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPostcomposeMap W X g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Z).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPostcomposeMap, Iso.hom_inv_id_assoc]

lemma reducedColimitIso_precompose {X Y : C} (Z : C) (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W Y Z).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPrecomposeMap W Z f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Z ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Z).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPrecomposeMap, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock

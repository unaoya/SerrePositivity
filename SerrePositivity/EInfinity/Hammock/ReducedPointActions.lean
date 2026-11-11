module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActions
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitArrowMap
public import SerrePositivity.EInfinity.Hammock.ReducedColimit

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
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

def reducedArrowMap {X Y : C} (f : X ⟶ Y) : 𝟙_ SSet.{max u v} ⟶ reducedSimplicialSet W X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f ≫ (reducedColimitIso W X Y).hom

def reducedPostcomposeMap (X : C) {Y Z : C} (g : Y ⟶ Z) :
    reducedSimplicialSet W X Y ⟶ reducedSimplicialSet W X Z :=
  (reducedColimitIso W X Y).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) ≫
    (reducedColimitIso W X Z).hom

def reducedPrecomposeMap {X Y : C} (Z : C) (f : X ⟶ Y) :
    reducedSimplicialSet W Y Z ⟶ reducedSimplicialSet W X Z :=
  (reducedColimitIso W Y Z).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Z ≫
    (reducedColimitIso W X Z).hom

lemma reducedColimitIso_postcompose (X : C) {Y Z : C} (g : Y ⟶ Z) :
    (reducedColimitIso W X Y).hom ≫ reducedPostcomposeMap W X g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) ≫ (reducedColimitIso W X Z).hom := by
  simp only [reducedPostcomposeMap, Iso.hom_inv_id_assoc]

lemma reducedColimitIso_precompose {X Y : C} (Z : C) (f : X ⟶ Y) :
    (reducedColimitIso W Y Z).hom ≫ reducedPrecomposeMap W Z f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Z ≫ (reducedColimitIso W X Z).hom := by
  simp only [reducedPrecomposeMap, Iso.hom_inv_id_assoc]

end SerrePositivity.EInfinity.Hammock

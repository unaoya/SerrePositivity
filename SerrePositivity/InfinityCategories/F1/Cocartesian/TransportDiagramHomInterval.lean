module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramRealizationVertices
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramRealizationEvaluation
public import SerrePositivity.InfinityCategories.F1.CoherentHomEquivalence
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostHomCriterion

/-!
概要：元の strict transport の全変換の core を、実現した図式間の区間模型へ写す。
方針：同じ coherent Hom 比較の区間を実現に後合成し、端点を元の図式に正規化する。
規約：比較の同値性は未証明であり、ここでは実際の作用とその展開を固定する。
使われ方：Cat∞ 値の分類主写像の充満忠実性に必要な Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の core の全 Hom を、実現した同じ二つの図式間の実際の区間族へ写す。 -/
def cocartesianTransportDiagramHomInterval {C : Type u} [Category.{u} C]
    (F G : CocartesianTransportDiagramCategory C) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom F G) ⟶
      intervalMappingSpace
        (functorVertex (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F)))
        (functorVertex (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor G))) :=
  coherentHomComparison F G ≫
    pinchedHomToIntervalMappingSpace (coherentNerveVertex F) (coherentNerveVertex G) ≫
      intervalMappingPostOfEq (cocartesianTransportDiagramRealization C)
        (coherentNerveVertex F) (coherentNerveVertex G)
        (cocartesianTransportDiagramRealization_vertex F)
        (cocartesianTransportDiagramRealization_vertex G)

/-- 実際の区間族を展開すると、元の Hom の prism を同じ実現へ後合成したもの。 -/
lemma cocartesianTransportDiagramHomInterval_uncurry
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) :
    intervalMappingUncurry (cocartesianTransportDiagramHomInterval F G) =
      rightMappingSpacePrism _ ≫ pinchedHomUncurry (coherentHomComparison F G) ≫
        cocartesianTransportDiagramRealization C := by
  rw [cocartesianTransportDiagramHomInterval, ← Category.assoc,
    intervalMappingPostOfEq_uncurry, pinchedHomToIntervalMappingSpace_uncurry]
  rfl

/-- 同じ全 Hom の区間族を底の対象で評価すると、元の core の豊穣評価の作用。 -/
lemma cocartesianTransportDiagramHomInterval_evaluate
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) (c : C) :
    intervalMappingUncurry (cocartesianTransportDiagramHomInterval F G) ≫
      evaluateFunctorAt (ULift.up (nerveVertex c)) =
    rightMappingSpacePrism _ ≫ pinchedHomUncurry (coherentHomComparison F G) ≫
      coherentNerveMap (cocartesianTransportDiagramEvaluationEnriched c) := by
  rw [cocartesianTransportDiagramHomInterval_uncurry, Category.assoc, Category.assoc,
    cocartesianTransportDiagramRealization_evaluate,
    cocartesianTransportDiagramInfinityEvaluation]

end SerrePositivity.InfinityCategories

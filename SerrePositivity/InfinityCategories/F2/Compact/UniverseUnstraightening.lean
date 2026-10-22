module

public import SerrePositivity.InfinityCategories.F2.Compact.YonedaEvaluationClassification
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityReconstruction

/-!
概要：指定した空間の宇宙変更の unstraightening と、元の全空間の底上の比較。
方針：元の評価の引き戻しを一段大きい空間値として分類し、実際の復元射を合成する。
規約：元の全空間・元の底・同じ宇宙変更を保持し、各 fiber の逆を別に選ばない。
使われ方：全空間の単位の弱同値を、宇宙変更後の余極限余錐へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の全空間の大きい分類図式は、指定した宇宙変更後の元の図式と全自然同型。 -/
def spaceUniverseUnstraightening_classificationIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    FunctorIso (leftStraighteningInfinityDiagram (leftUnstraighteningProjection F))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}) :=
  (leftStraighteningInfinityDiagram_baseChangeIso pointedSpaceProjection F).symm

/-- 元の全空間から、同じ宇宙変更をした図式の小さい unstraightening への実際の比較。 -/
def spaceUniverseUnstraighteningComparison {B : SSet.{u + 1}} [Quasicategory B]
    (F : B ⟶ SpaceInfinity.{u}) :
    leftUnstraightening F ⟶ smallLeftUnstraightening
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}) :=
  leftStraighteningInfinityReconstruction (leftUnstraighteningProjection F) ≫
    smallLeftUnstraighteningComparisonOfFunctorIso
      (spaceUniverseUnstraightening_classificationIso F)

/-- 元の全空間の比較は、元の底への実際の射影を厳密に保つ。 -/
lemma spaceUniverseUnstraighteningComparison_projection {B : SSet.{u + 1}} [Quasicategory B]
    (F : B ⟶ SpaceInfinity.{u}) :
    spaceUniverseUnstraighteningComparison F ≫ smallLeftUnstraighteningProjection
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}) =
      leftUnstraighteningProjection F := by
  rw [spaceUniverseUnstraighteningComparison, Category.assoc,
    smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    leftStraighteningInfinityReconstruction_projection]

/-- 構成した同じ全空間の比較自身は、任意の大きい quasicategory 標的への前合成同値。 -/
lemma spaceUniverseUnstraighteningComparison_isPrecompositionEquivalence
    {B : SSet.{u + 1}} [Quasicategory B] (F : B ⟶ SpaceInfinity.{u}) :
    IsPrecompositionEquivalence (spaceUniverseUnstraighteningComparison F) :=
  (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence
    (leftUnstraighteningProjection F)).comp
      (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence _)

end SerrePositivity.InfinityCategories.F2.Compact

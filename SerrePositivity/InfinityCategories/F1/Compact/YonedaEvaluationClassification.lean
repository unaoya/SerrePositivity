module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.CovariantRepresentableInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.Compact.ClassificationTransport
public import SerrePositivity.InfinityCategories.F1B.Compact.RepresentableCoslice
public import SerrePositivity.InfinityCategories.F1.Compact.YonedaEvaluationCoslice
public import SerrePositivity.InfinityCategories.F1.Compact.YonedaEvaluationEquivalence

/-!
概要：元の Yoneda 対象からの全共変 Hom 関手と、元の前層評価の全分類図式の比較。
方針：構成した一つの底上の大域比較を分類関手で送り、元の coslice 比較を合成する。
規約：小さい空間の宇宙変更も元の pointed-space 射影の分類図式として固定する。
使われ方：この同じ宇宙変更の小さい余極限保存と、元の評価保存から compact 性を導く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 同じ pointed-space 射影を一段大きい空間値として分類する、元の宇宙変更の図式。 -/
def spaceUniverseDiagram :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj SpaceInfinity.{u} ⟶ SpaceInfinity.{u + 1} :=
  leftStraighteningInfinityDiagram pointedSpaceProjection.{u}

/-- 元の Yoneda 対象からの全 Hom 関手は、元の評価の全空間そのものの分類図式。 -/
def yonedaEvaluation_classificationIso {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity (functorVertex (representablePresheafInfinity y)))
      (leftStraighteningInfinityDiagram
        (leftUnstraighteningProjection (presheafInfinityEvaluation y))) :=
  covariantRepresentableInfinity_cosliceIso _ ≪≫
    leftClassification_of_precompositionEquivalence _ _ (yonedaEvaluationCosliceMap y)
      (yonedaEvaluationCosliceMap_projection y)
      (yonedaEvaluationCosliceMap_isPrecompositionEquivalence y)

/-- 元の Yoneda 対象からの全 Hom 関手は、同じ評価と指定した宇宙変更の合成。 -/
def yonedaEvaluation_universeIso {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity (functorVertex (representablePresheafInfinity y)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (presheafInfinityEvaluation y) ≫
        spaceUniverseDiagram.{u}) :=
  yonedaEvaluation_classificationIso y ≪≫
    (leftStraighteningInfinityDiagram_baseChangeIso pointedSpaceProjection
      (presheafInfinityEvaluation y)).symm

/-- 同じ全比較は、元の Yoneda 埋め込みの指定頂点そのものに対して成立する。 -/
def yonedaInfinityMap_evaluationIso {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity
      ((yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (presheafInfinityEvaluation y) ≫
        spaceUniverseDiagram.{u}) := by
  rw [yonedaInfinityMap_vertex]
  exact yonedaEvaluation_universeIso y

end SerrePositivity.InfinityCategories.F2.Compact

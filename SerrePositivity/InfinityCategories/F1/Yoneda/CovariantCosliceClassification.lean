module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomInfinityBifunctor
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaSourceBaseChange
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourceInitial
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningEssentialSurjectivity
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningLift

/-!
概要：元の coslice の分類図式を、指定された共変 Hom 全図式へ結ぶ。
方針：始点固定 twisted arrow への同じ全空間同値を分類し、底変換同型を合成する。
規約：点ごとの値同値を入力にせず、底を保つ全空間同値を使う。
使われ方：表現可能な Kan 値 coherent 図式の全図式比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の coslice の分類図式は指定された共変 Hom 図式に同型。 -/
def covariantCosliceClassificationIso {B : SSet.{u}} [Quasicategory B] (x : B _⦋0⦌) :
    FunctorIso (leftStraighteningInfinityDiagram
      (sliceUnderProjection (SSet.yonedaEquiv.symm x))) (homInfinityCovariant x) := by
  have e := VertexIso.map (leftFibrationInfinityVertexIsoOfPrecompositionEquivalence
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) (twistedArrowSourceProjection x)
    (cosliceToTwistedArrowSource x) (cosliceToTwistedArrowSource_projection x)
    (cosliceToTwistedArrowSource_isPrecompositionEquivalence x)) (leftStraighteningInfinityMap B)
  rw [← leftStraighteningInfinityDiagram_vertex, ← leftStraighteningInfinityDiagram_vertex] at e
  have r := yonedaInfinityMap_evaluation_sourceIso x
  rw [← homInfinityCovariant_eq_yonedaEvaluation] at r
  exact e ≪≫ r.symm

/-- 全 coslice から元の unstraightening への底上同値は、全図式同型を与える。 -/
def covariantHomIsoOfCosliceEquivalence {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (x : B _⦋0⦌)
    (f : (SSet.uliftFunctor.{u + 1, u}).obj
      (sliceUnder (SSet.yonedaEquiv.symm x)) ⟶ leftUnstraightening F)
    (hf : f ≫ leftUnstraighteningProjection F =
      (SSet.uliftFunctor.{u + 1, u}).map (sliceUnderProjection (SSet.yonedaEquiv.symm x)))
    (he : IsPrecompositionEquivalence f) : FunctorIso F (homInfinityCovariant x) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let q := smallLeftUnstraighteningProjection F
  let g := smallLeftUnstraighteningLift F f
  have h := smallLeftUnstraighteningLift_projection F p f hf
  have e := VertexIso.map (leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p q g h
    (smallLeftUnstraighteningLift_isPrecompositionEquivalence F p f hf he))
    (leftStraighteningInfinityMap B)
  rw [← leftStraighteningInfinityDiagram_vertex, ← leftStraighteningInfinityDiagram_vertex] at e
  exact (leftStraighteningInfinityCounit F).symm ≪≫ e.symm ≪≫ covariantCosliceClassificationIso x

end SerrePositivity.InfinityCategories

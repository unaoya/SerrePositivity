module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningEssentialSurjectivity
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningLift
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinityEquivalence

/-!
概要：実際の straightening の図式から元の小さい left fibration を復元する成分。
方針：相対表現の比較を元の宇宙へ降ろし、分類図式の同型による unstraightening と合成する。
規約：底が quasicategory の場合。成分の同値性と全対象の自然性を区別する。
使われ方：§5.6.5 の分類の単位成分と、残る三角恒等式への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 小さい全空間の持ち上げに、構成済みの相対表現の存在を適用する。 -/
def nativeLeftTransportRepresentation {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p) := by
  have (n : SimplexCategoryᵒᵖ) : Small.{u} ((SSet.uliftFunctor.{u + 1, u}).obj E |>.obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (E.obj n)))
  exact smallFiberLeftStraighteningRepresentation _ (hasSmallSimplexFibers_of_small_total _)

/-- 元の left fibration から選択した表現の小さい unstraightening への比較。 -/
def nativeLeftTransportComparison {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    E ⟶ smallLeftUnstraightening (nativeLeftTransportRepresentation p).diagram :=
  smallLeftUnstraighteningLift _ (nativeLeftTransportRepresentation p).comparison

/-- この比較は、元の宇宙で底を厳密に保つ。 -/
lemma nativeLeftTransportComparison_projection {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    nativeLeftTransportComparison p ≫
      smallLeftUnstraighteningProjection (nativeLeftTransportRepresentation p).diagram = p :=
  smallLeftUnstraighteningLift_projection _ p _ (nativeLeftTransportRepresentation p).over_base

/-- 元の底が quasicategory なら、降ろした比較も前合成同値。 -/
lemma nativeLeftTransportComparison_isPrecompositionEquivalence {E B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) [LeftFibration p] :
    IsPrecompositionEquivalence (nativeLeftTransportComparison p) :=
  smallLeftUnstraighteningLift_isPrecompositionEquivalence _ p _
    (nativeLeftTransportRepresentation p).over_base
    (nativeLeftTransportRepresentation p).isPrecompositionEquivalence

/-- 実際の straightening の図式の小さい unstraightening への復元射。 -/
def leftStraighteningInfinityReconstruction {E B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) [LeftFibration p] :
    E ⟶ smallLeftUnstraightening (leftStraighteningInfinityDiagram p) :=
  nativeLeftTransportComparison p ≫ smallLeftUnstraighteningComparisonOfFunctorIso
    (leftStraighteningInfinityDiagram_representationIso p
      (nativeLeftTransportRepresentation p)).symm

/-- 実際の straightening からの復元射は底を厳密に保つ。 -/
lemma leftStraighteningInfinityReconstruction_projection {E B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) [LeftFibration p] :
    leftStraighteningInfinityReconstruction p ≫
      smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) = p := by
  rw [leftStraighteningInfinityReconstruction, Category.assoc,
    smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    nativeLeftTransportComparison_projection]

/-- 同じ実際の復元射は前合成同値。 -/
lemma leftStraighteningInfinityReconstruction_isPrecompositionEquivalence {E B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) [LeftFibration p] :
    IsPrecompositionEquivalence (leftStraighteningInfinityReconstruction p) :=
  (nativeLeftTransportComparison_isPrecompositionEquivalence p).comp
    (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence _)

/-- 復元射は left fibrations の実際の coherent nerve で単位の同型成分を与える。 -/
def leftStraighteningInfinityUnitVertex {E B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) [LeftFibration p] :
    VertexIso (leftFibrationInfinityVertex p)
      (leftFibrationInfinityVertex
        (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))) :=
  leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p _
    (leftStraighteningInfinityReconstruction p)
    (leftStraighteningInfinityReconstruction_projection p)
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p)

end SerrePositivity.InfinityCategories

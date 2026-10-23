module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductScaffoldEquivalence
public import SerrePositivity.InfinityCategories.F2.Ind.SpanLeftFibrationComparison
public import SerrePositivity.InfinityCategories.F1.Diagrams.OverComparisonResolution
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningBaseChange

/-!
概要：元の共同 weighted 分類の初頂点制限と、全単体切断の weighted 分類の大域同型。
方針：元の二つの scaffold の共通置換を底上の分類頂点の同型へ移す。
規約：元の積添字全体に一つの同型を与え、値ごとの比較で代用しない。
使われ方：strict 分類像と共同分類の全高次を保つ比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B)

/-- 同じ二つの大域 scaffold を延長した共通 span が与える分類頂点の同型。 -/
def sectionProductClassificationVertexIso :
    VertexIso
      (leftFibrationInfinityVertex
        (pullback.snd (leftFibrationWeightedProjection F) (sectionProductBaseMap I B)))
      (leftFibrationInfinityVertex
        (weightedNerveProjection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget))) := Classical.choice (show Nonempty _ from by
  obtain ⟨Z, j, t, a, b, hj, ht, hjt, hja, hjb, hat, hbt, ea, eb⟩ :=
    exists_innerFibration_comparison_span
      (simplicialReplacementProjection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget))
      (pullback.snd (leftFibrationWeightedProjection F) (sectionProductBaseMap I B))
      (weightedNerveProjection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget))
      (sectionProductScaffold F)
      (tautScaffold (strictLeftTransportSectionDiagram F ⋙ kanObjectForget))
      (sectionProductScaffold_projection F)
      (tautScaffold_projection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget))
      (sectionProductScaffold_isPrecompositionEquivalence F)
      (tautScaffold_isPrecompositionEquivalence
        (strictLeftTransportSectionDiagram F ⋙ kanObjectForget))
  have : InnerFibration t := ht
  exact ⟨leftFibrationVertexIsoOfSpan _ _ t a b hat hbt ea eb⟩)

/-- 初頂点引き戻しと全切断 weighted nerve の分類は、一つの全添字上の関手同型。 -/
def sectionProductPullbackClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        (pullback.snd (leftFibrationWeightedProjection F) (sectionProductBaseMap I B)))
      (leftStraighteningInfinityDiagram
        (weightedNerveProjection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget))) := by
  have h := (sectionProductClassificationVertexIso F).map
    (leftStraighteningInfinityMap (nerve (I × TransportSimplexCategory B)))
  rw [← leftStraighteningInfinityDiagram_vertex,
    ← leftStraighteningInfinityDiagram_vertex] at h
  exact h

/-- 元の共同分類そのものを初頂点で制限すると、全切断の weighted 分類と大域的に同型。 -/
def sectionProductClassificationIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (sectionProductBaseMap I B) ≫
        leftStraighteningInfinityDiagram (leftFibrationWeightedProjection F))
      (leftStraighteningInfinityDiagram
        (weightedNerveProjection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget))) :=
  leftStraighteningInfinityDiagram_baseChangeIso (leftFibrationWeightedProjection F)
    (sectionProductBaseMap I B) ≪≫ sectionProductPullbackClassificationIso F

end SerrePositivity.InfinityCategories.F2.Ind

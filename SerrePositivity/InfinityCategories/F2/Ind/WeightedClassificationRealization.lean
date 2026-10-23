module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveStraighteningUnit
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.F1.Transport.NerveTransportRepresentation

/-!
概要：Kan 値の通常の図式の weighted 分類を、元の全 coherent 図式へ戻す。
方針：共同 weighted 単位を元の図式で評価し、実際の分類を nerve 上の表現へ比較する。
規約：全底上の一つの関手同型。値ごとの同型を選ぶ証明ではない。
使われ方：全単体切断の weighted 分類と strict 分類像の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

instance kanDiagramUnderlying_kan {K : Type u} [Category.{u} K]
    (H : K ⥤ KanObject.{u}) (k : K) : KanComplex ((H ⋙ kanObjectForget).obj k) :=
  (H.obj k).isKanComplex

/-- 共同 weighted 単位の同じ図式での成分は、元の図式全体を復元する。 -/
def weightedCandidateRealizationIso {K : Type u} [Category.{u} K] (H : K ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve H)
      (leftStraighteningCandidate (weightedNerveProjection (H ⋙ kanObjectForget))) := by
  let X : KanDiagramObject K := ⟨H, trivial⟩
  have h := VertexIso.map (weightedNerveStraighteningCoherentUnitIso K)
    (evaluateFunctorAt (coherentNerveVertex X))
  have hv : (weightedNerveInfinityMap K).app (Opposite.op ⦋0⦌) (coherentNerveVertex X) =
      leftFibrationInfinityVertex (weightedNerveProjection (H ⋙ kanObjectForget)) :=
    coherentNerveMap_vertex (weightedNerveKanEnriched K) X
  have ht : (weightedNerveInfinityMap K ≫ leftStraighteningCoherentMap K).app
      (Opposite.op ⦋0⦌) (coherentNerveVertex X) =
        functorVertex (leftStraighteningCandidate
          (weightedNerveProjection (H ⋙ kanObjectForget))) := by
    exact (congrArg ((leftStraighteningCoherentMap K).app (Opposite.op ⦋0⦌)) hv).trans
      (leftStraighteningCoherentMap_vertex _)
  exact (eqToIso (congrArg HomotopyCategory.mk (kanDiagramRealization_vertex X))).symm ≪≫
    h ≪≫ eqToIso (congrArg HomotopyCategory.mk ht)

/-- 実際の weighted 分類は、元の Kan 図式の同じ全高次の実現と関手同型。 -/
def weightedClassificationRealizationIso {K : Type u} [Category.{u} K]
    (H : K ⥤ KanObject.{u}) :
    FunctorIso (leftStraighteningInfinityDiagram
      (weightedNerveProjection (H ⋙ kanObjectForget))) (kanDiagramCoherentNerve H) :=
  leftStraighteningInfinityDiagram_representationIso _ (nerveLeftTransportRepresentation _) ≪≫
    (leftStraighteningCoherentMap_oppositeVertexIso _).symm ≪≫
      (weightedCandidateRealizationIso H).symm

end SerrePositivity.InfinityCategories.F2.Ind

module

public import SerrePositivity.InfinityCategories.F1.Transport.WitnessPrism
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationWitness

/-!
概要：表現空間の辺による図式の変換の unstraightening は実際の表現の比較を回収する。
方針：同じ辺の全空間側の prism を具体的な持ち上げとして選択独立性へ渡す。
規約：比較は同じ底上の相対写像空間内で取る。
使われ方：coherent な復元の単位と変換への作用の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準表現からの表現の辺の全空間側 prism は標準の pointed-space 射から始まる。
方針：prism の始点を標準表現の恒等比較で計算する。
規約：底の分類図式は F。
使われ方：unstraightening の変換の具体的な持ち上げの初期条件。 -/
lemma transportRepresentationEdgePrism_start {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (R : LeftTransportRepresentation (leftUnstraighteningProjection F))
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj (transportWitnessSpace (leftUnstraighteningProjection F)))
      (transportWitnessVertex (unstraighteningTransportRepresentation F))
      (transportWitnessVertex R)) :
    prismEndpoint 0 _ ≫ functorEdgePrism (transportWitnessSpacePointedEdge e) =
      pullback.fst pointedSpaceProjection F := by
  have h := functorEdgePrism_zero (transportWitnessSpacePointedEdge e)
  simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
    Category.id_comp] using h

/-- 概要：表現の辺に沿う変換の unstraightening はその表現の比較射と底上で同型。
方針：全空間側の prism を持ち上げの選択空間の頂点として回収し終点を比較する。
規約：元の表現の比較射そのものを終点とする。
使われ方：復元の単位成分と unstraightening の変換の整合性。 -/
def transportRepresentationEdge_comparisonIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (R : LeftTransportRepresentation (leftUnstraighteningProjection F))
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj (transportWitnessSpace (leftUnstraighteningProjection F)))
      (transportWitnessVertex (unstraighteningTransportRepresentation F))
      (transportWitnessVertex R)) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection R.diagram)
      (leftUnstraighteningProjection F)
      (leftUnstraighteningTransformationMap F R.diagram
        (functorEdgePrism (transportWitnessSpaceDiagramEdge e))
        (functorEdgePrism_zero _) (functorEdgePrism_one _)).val
      (leftUnstraighteningTransformationMap F R.diagram
        (functorEdgePrism (transportWitnessSpaceDiagramEdge e))
        (functorEdgePrism_zero _) (functorEdgePrism_one _)).property)
      (relativeFunctorVertex (leftUnstraighteningProjection R.diagram)
        (leftUnstraighteningProjection F) R.comparison R.over_base) := by
  let H := functorEdgePrism (transportWitnessSpaceDiagramEdge e)
  let W := functorEdgePrism (transportWitnessSpacePointedEdge e)
  have h0 : prismEndpoint 0 B ≫ H = F := functorEdgePrism_zero _
  have h1 : prismEndpoint 1 B ≫ H = R.diagram := functorEdgePrism_one _
  have hw0 : prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F :=
    transportRepresentationEdgePrism_start F R e
  have hwp : W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H :=
    transportWitnessSpaceEdgePrism_condition e
  have hw1 : prismEndpoint 1 _ ≫ W = R.comparison ≫
      pullback.fst pointedSpaceProjection R.diagram := functorEdgePrism_one _
  have h := leftUnstraighteningTransformationMapChoiceIso F R.diagram H h0 h1
    (leftUnstraighteningTransformationWitness F H h0 W hw0 hwp)
  rw [leftUnstraighteningTransformationWitness_endpoint F R.diagram H h0 h1 W hw0 hwp
    R.comparison R.over_base hw1] at h
  exact h

end SerrePositivity.InfinityCategories

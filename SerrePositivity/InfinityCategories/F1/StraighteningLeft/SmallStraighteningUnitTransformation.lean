module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallStraighteningCounit
public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationEdgeComparison

/-!
概要：coherent な図式からその復元への単位変換と全空間比較との整合性。
方針：標準表現から選んだ表現への辺を同じ可縮空間内で取り変換と持ち上げへ写す。
規約：対象ごとの成分を構成し全対象にわたる自然性は後続に残す。
使われ方：一般の単位と unstraightening の実際の作用を結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準表現から選んだ復元の表現への具体的な辺。
方針：可縮な表現空間で選んだ頂点の終対象性を使う。
規約：二つの端点を厳密に固定する。
使われ方：単位の図式と全空間側の同時の変換。 -/
def smallCoherentStraighteningUnitWitnessEdge {B : SSet.{u + 1}}
    [∀ m, Small.{u} (B.obj m)] (F : B ⟶ SpaceInfinity.{u}) :
    SSet.Truncated.Edge
      (X := (truncation 2).obj (transportWitnessSpace (leftUnstraighteningProjection F)))
      (transportWitnessVertex (unstraighteningTransportRepresentation F))
      (transportWitnessVertex
        (smallLeftStraighteningRepresentation (leftUnstraighteningProjection F))) :=
  Classical.choice (((coherentUnstraighteningWitnessSpace_isContractibleKan F).isTerminalVertex
    (transportWitnessVertex
      (smallLeftStraighteningRepresentation (leftUnstraighteningProjection F)))).nonempty_edge
        (transportWitnessVertex (unstraighteningTransportRepresentation F)))

/-- 概要：任意の coherent な図式から unstraightening を分類して得る図式への単位変換。
方針：表現空間の具体的な辺を分類図式の prism へ写す。
規約：底を通常の圏の nerve に限定しない。
使われ方：straightening と unstraightening の単位の成分。 -/
def smallCoherentStraighteningUnitTransformation {B : SSet.{u + 1}}
    [∀ m, Small.{u} (B.obj m)] (F : B ⟶ SpaceInfinity.{u}) :
    (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u} :=
  functorEdgePrism (transportWitnessSpaceDiagramEdge (smallCoherentStraighteningUnitWitnessEdge F))

/-- 概要：単位変換の始点は元の coherent な図式。
方針：表現の辺の分類図式の始点を回収する。
規約：厳密な等式。
使われ方：unstraightening の変換の作用の始域の指定。 -/
lemma smallCoherentStraighteningUnitTransformation_zero {B : SSet.{u + 1}}
    [∀ m, Small.{u} (B.obj m)] (F : B ⟶ SpaceInfinity.{u}) :
    prismEndpoint 0 B ≫ smallCoherentStraighteningUnitTransformation F = F :=
  functorEdgePrism_zero _

/-- 概要：単位変換の終点は復元した coherent な図式。
方針：表現の辺の分類図式の終点を回収する。
規約：厳密な等式。
使われ方：unstraightening の変換の作用の終域の指定。 -/
lemma smallCoherentStraighteningUnitTransformation_one {B : SSet.{u + 1}}
    [∀ m, Small.{u} (B.obj m)] (F : B ⟶ SpaceInfinity.{u}) :
    prismEndpoint 1 B ≫ smallCoherentStraighteningUnitTransformation F =
      smallLeftStraighteningDiagram (leftUnstraighteningProjection F) :=
  functorEdgePrism_one _

/-- 概要：単位変換の unstraightening は選んだ復元の比較射と底上の写像空間で同型。
方針：同じ表現の辺の全空間側の prism を具体的な持ち上げとして使う。
規約：選択した図式と実際の全空間比較を結ぶ。
使われ方：一般の単位成分と unstraightening の作用の整合性。 -/
def smallCoherentStraighteningUnitTransformation_comparisonIso {B : SSet.{u + 1}}
    [∀ m, Small.{u} (B.obj m)] (F : B ⟶ SpaceInfinity.{u}) :
    VertexIso (relativeFunctorVertex
      (leftUnstraighteningProjection
        (smallLeftStraighteningDiagram (leftUnstraighteningProjection F)))
      (leftUnstraighteningProjection F)
      (leftUnstraighteningTransformationMap F
        (smallLeftStraighteningDiagram (leftUnstraighteningProjection F))
        (smallCoherentStraighteningUnitTransformation F)
        (smallCoherentStraighteningUnitTransformation_zero F)
        (smallCoherentStraighteningUnitTransformation_one F)).val
      (leftUnstraighteningTransformationMap F
        (smallLeftStraighteningDiagram (leftUnstraighteningProjection F))
        (smallCoherentStraighteningUnitTransformation F)
        (smallCoherentStraighteningUnitTransformation_zero F)
        (smallCoherentStraighteningUnitTransformation_one F)).property)
      (relativeFunctorVertex
        (leftUnstraighteningProjection
        (smallLeftStraighteningDiagram (leftUnstraighteningProjection F)))
        (leftUnstraighteningProjection F)
        (smallLeftStraighteningComparison (leftUnstraighteningProjection F))
        (smallLeftStraighteningComparison_over_base (leftUnstraighteningProjection F))) :=
  transportRepresentationEdge_comparisonIso F
    (smallLeftStraighteningRepresentation (leftUnstraighteningProjection F))
    (smallCoherentStraighteningUnitWitnessEdge F)

end SerrePositivity.InfinityCategories

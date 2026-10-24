module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCoconeLegTriangles
public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpanCocone
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransportComparison
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyPathReplacement
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：部分余極限 span の普遍余錐の実際の二単体から、左右の輸送を比較する指定経路族を作る。
方針：二つの合成三角形を輸送の合成同型へ移し、その合成のホモトピーを経路へ変換する。
規約：共通部分の fiber の全パラメータを保つ。使われ方：貼り合わせの指定境界経路の中心部分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C : SSet.{u + 1}} {p : A ⟶ SpaceInfinity.{u}}
  (c : JoinCocone p) (hc : IsColimitCone c)
  (i : A ⟶ B) (F : B ⟶ SpaceInfinity.{u}) (hi : i ≫ F = p) (dB : JoinCocone F)
  (j : A ⟶ C) (G : C ⟶ SpaceInfinity.{u}) (hj : j ≫ G = p) (dC : JoinCocone G)

/-- span の共通始点から普遍余錐の頂点への実際の脚。 -/
def partialColimitSpanRootLeg :
    SpaceInfinity.Edge c.vertex (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex :=
  strictCoconeVertexLeg _ (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC)
    (AsSmall.up.obj WalkingSpan.zero) c.vertex (coherentNerveVertex_object c.vertex)

/-- 左比較辺と左脚の合成を表す、span の普遍余錐の元の二単体。 -/
def partialColimitSpanLeftTriangle :
    SSet.Edge.CompStruct (SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc i F hi dB))
      (partialColimitSpanLeftLeg c hc i F hi dB j G hj dC)
      (partialColimitSpanRootLeg c hc i F hi dB j G hj dC) :=
  strictCoconeVertexLegCompStruct _ _ (AsSmall.up.map WalkingSpan.Hom.fst)
    (coherentNerveVertex_object c.vertex) (coherentNerveVertex_object dB.vertex)
    (SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc i F hi dB))
    (colimitAttachmentApexHom_edge c hc i F hi dB).symm

/-- 右比較辺と右脚の合成も、同じ共通脚への実際の二単体で指定される。 -/
def partialColimitSpanRightTriangle :
    SSet.Edge.CompStruct (SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc j G hj dC))
      (partialColimitSpanRightLeg c hc i F hi dB j G hj dC)
      (partialColimitSpanRootLeg c hc i F hi dB j G hj dC) :=
  strictCoconeVertexLegCompStruct _ _ (AsSmall.up.map WalkingSpan.Hom.snd)
    (coherentNerveVertex_object c.vertex) (coherentNerveVertex_object dC.vertex)
    (SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc j G hj dC))
    (colimitAttachmentApexHom_edge c hc j G hj dC).symm

variable {E : SSet.{u + 1}} (q : E ⟶ SpaceInfinity.{u}) [LeftFibration q]

/-- 同じ実際の共通脚を持つ二つの三角形による、左右の二段階輸送の指定された同型。 -/
def partialColimitSpanTransportIso :
    FunctorIso
      (edgeTransport q (colimitAttachmentApexEdge c hc i F hi dB) ≫
        edgeTransport q (partialColimitSpanLeftLeg c hc i F hi dB j G hj dC))
      (edgeTransport q (colimitAttachmentApexEdge c hc j G hj dC) ≫
        edgeTransport q (partialColimitSpanRightLeg c hc i F hi dB j G hj dC)) :=
  coherentTransportTriangleCompositionIso q
    (partialColimitSpanLeftTriangle c hc i F hi dB j G hj dC) ≪≫
      (coherentTransportTriangleCompositionIso q
        (partialColimitSpanRightTriangle c hc i F hi dB j G hj dC)).symm

/-- span の元の二単体により指定された、共通始点の fiber の全パラメータの境界経路族。 -/
def partialColimitSpanTransportPath :
    vertexFiber q c.vertex ⟶ equivalencePath
      (vertexFiber q (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex) := by
  have := vertexFiber_kanComplex_of_leftFibration q
    (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex
  exact homotopyEquivalencePath
    (partialColimitSpanTransportIso c hc i F hi dB j G hj dC q).simplicialHomotopy

/-- 指定経路族の始点は、実際の左比較辺と左脚に沿う二段階輸送。 -/
lemma partialColimitSpanTransportPath_zero :
    partialColimitSpanTransportPath c hc i F hi dB j G hj dC q ≫ equivalencePathEndpoint _ 0 =
      edgeTransport q (colimitAttachmentApexEdge c hc i F hi dB) ≫
        edgeTransport q (partialColimitSpanLeftLeg c hc i F hi dB j G hj dC) := by
  have := vertexFiber_kanComplex_of_leftFibration q
    (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex
  exact homotopyEquivalencePath_zero _

/-- 指定経路族の終点は、実際の右比較辺と右脚に沿う二段階輸送。 -/
lemma partialColimitSpanTransportPath_one :
    partialColimitSpanTransportPath c hc i F hi dB j G hj dC q ≫ equivalencePathEndpoint _ 1 =
      edgeTransport q (colimitAttachmentApexEdge c hc j G hj dC) ≫
        edgeTransport q (partialColimitSpanRightLeg c hc i F hi dB j G hj dC) := by
  have := vertexFiber_kanComplex_of_leftFibration q
    (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex
  exact homotopyEquivalencePath_one _

end
end SerrePositivity.InfinityCategories.HomotopyLimits

module
public import SerrePositivity.KST.Fibration.FractionCosliceBaseChange
public import SerrePositivity.KST.Fibration.StrictTransportPostEvaluation
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertex

/-! # 元の全分数評価による、全単体圏上の coherent な写像空間比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (x : X _⦋0⦌)

/-- 同じ商像の coslice を、元の全単体圏の初頂点図式へ厳密に引き戻す。 -/
def fractionSimplexCosliceProjection :
    pullback (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
        (transportSimplexFirstVertexMap X ≫ F) ⟶ nerve (TransportSimplexCategory X) :=
  pullback.snd _ _

instance fractionSimplexCosliceProjection_leftFibration :
    LeftFibration (fractionSimplexCosliceProjection F x) :=
  inferInstanceAs (LeftFibration (pullback.snd _ _))

/-- 商の元の coslice fiber を表す、同じ strict Kan 図式。 -/
def fractionSimplexKanMappingDiagram : TransportSimplexCategory X ⥤ KanObject.{u} :=
  cocartesianKanDiagram (fractionSimplexCosliceProjection F x)

/-- 元の全 span 族の評価は、同じ全単体上の Kan 図式を一つの自然変換で結ぶ。 -/
def fractionSimplexKanComparison :
    cocartesianKanDiagram (pullback.snd (markedSpanFamilyProjection X W x)
      (transportSimplexFirstVertexMap X)) ⟶ fractionSimplexKanMappingDiagram F x :=
  strictKanTransportPostToLeftFibration _ _
    (fractionCosliceBaseChange F W hF x (transportSimplexFirstVertexMap X))
    (fractionCosliceBaseChange_snd F W hF x (transportSimplexFirstVertexMap X))

/-- 同じ自然変換の全高次の整合性を、元の coherent な図式間の実辺として保持する。 -/
def fractionSimplexKanComparisonEdge :
    Edge (functorVertex (cocartesianKanCoherentDiagram
      (pullback.snd (markedSpanFamilyProjection X W x) (transportSimplexFirstVertexMap X))))
      (functorVertex (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram F x))) :=
  strictKanTransportPostToLeftFibrationEdge _ _
    (fractionCosliceBaseChange F W hF x (transportSimplexFirstVertexMap X))
    (fractionCosliceBaseChange_snd F W hF x (transportSimplexFirstVertexMap X))

end SerrePositivity.KST.Fibration

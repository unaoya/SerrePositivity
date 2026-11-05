module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionCosliceBaseChange
public import SerrePositivity.KST.Fibration.StrictTransportPostEvaluation
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertex

/-! # 元の全分数評価による、全単体圏上の coherent な写像空間比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
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

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexCosliceProjection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexCosliceProjection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexCosliceProjection

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexCosliceProjection_leftFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexCosliceProjection_leftFibration := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexCosliceProjection_leftFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexKanComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanComparisonEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexKanComparisonEdge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanComparisonEdge

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexKanMappingDiagram := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexCosliceProjection._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexCosliceProjection._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexKanComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexKanComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanComparison._proof_2

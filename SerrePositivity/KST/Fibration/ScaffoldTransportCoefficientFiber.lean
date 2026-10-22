module
public import SerrePositivity.KST.Fibration.ScaffoldTransportCoefficientTriangle
public import SerrePositivity.KST.Fibration.CosliceTransportPointHom

/-! # 元の係数点の三角を、底を固定した同じ unstraightening fiber 内で比較する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace ScaffoldTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : ScaffoldTransportComparisonSpan p)

/-- 元の係数値から、同じ scaffold の埋め込みを通って共通全空間に入る。 -/
def coefficientEmbedding (c : I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (leftStrictTransport p c) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj s.total :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (simplicialReplacementConstantLift (leftStrictTransportDiagram p) c ≫ s.embedding)

/-- 元の係数値の底を、宇宙と始域を固定して表示する。 -/
def coefficientBase (c : I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (leftStrictTransport p c) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) :=
  SSet.const (ULift.up (nerveVertex c))

/-- 同じ係数値上では共通底は元の指定頂点に厳密に定値。 -/
theorem coefficientEmbedding_over (c : I) :
    s.coefficientEmbedding c ≫ s.toStrictTransportComparisonSpan.coherentBase =
      coefficientBase (p := p) c := by
  rw [coefficientEmbedding, StrictTransportComparisonSpan.coherentBase,
    ← Functor.map_comp, Category.assoc, s.embedding_over,
    simplicialReplacementConstantLift_projection]
  rfl

/-- 相対三角を係数値に制限し、その指定点で評価する同じ fiber への写像。 -/
def coefficientRelativeEvaluation (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    relativeFunctorSpace (leftUnstraighteningProjection (leftCoherentTransport p))
      s.toStrictTransportComparisonSpan.coherentBase ⟶
        vertexFiber (leftUnstraighteningProjection (leftCoherentTransport p))
          (ULift.up (nerveVertex c)) :=
  relativeFunctorOverPre (leftUnstraighteningProjection (leftCoherentTransport p))
    (Over.homMk (U := Over.mk (coefficientBase (p := p) c))
      (V := Over.mk s.toStrictTransportComparisonSpan.coherentBase)
      (s.coefficientEmbedding c) (s.coefficientEmbedding_over c)) ≫
    relativeFunctorEvaluate (leftUnstraighteningProjection (leftCoherentTransport p))
      (coefficientBase (p := p) c) (ULift.up v)

/-- 元の係数点から得る、同じ表現の実 fiber 点。 -/
def coefficientSourceFiberPoint (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (vertexFiber (leftUnstraighteningProjection (leftCoherentTransport p))
      (ULift.up (nerveVertex c))) _⦋0⦌ :=
  (s.coefficientRelativeEvaluation c v).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _
      (s.toStrictTransportComparisonSpan.coherentSource ≫
        s.toStrictTransportComparisonSpan.coherentComparison.hom)
      (by rw [Category.assoc, s.toStrictTransportComparisonSpan.coherentComparison.over,
        s.toStrictTransportComparisonSpan.coherentSource_over]))

/-- 同じ係数点の weighted 脚による、同じ底の実 fiber 点。 -/
def coefficientWeightedFiberPoint (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (vertexFiber (leftUnstraighteningProjection (leftCoherentTransport p))
      (ULift.up (nerveVertex c))) _⦋0⦌ :=
  (s.coefficientRelativeEvaluation c v).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _ s.toStrictTransportComparisonSpan.coherentTarget
      s.toStrictTransportComparisonSpan.coherentTarget_over)

/-- 元の係数点の source と weighted 像は、底を固定した同じ fiber 内で同型。 -/
def coefficientFiberPointIso (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    VertexIso (s.coefficientSourceFiberPoint c v) (s.coefficientWeightedFiberPoint c v) :=
  VertexIso.map s.toStrictTransportComparisonSpan.coherentComparison.triangle
    (s.coefficientRelativeEvaluation c v)

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration

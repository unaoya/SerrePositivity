module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportCoefficientFiber
public import SerrePositivity.KST.Fibration.ScaffoldTransportCoefficientTriangle
public import SerrePositivity.InfinityCategories.F1.Transport.CosliceTransportPointHom

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
  {p : E ⟶ nerve I} [LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan p)

/-- 元の係数点から得る、同じ表現の実 fiber 点。 -/
def coefficientSourceFiberPoint (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (vertexFiber (leftUnstraighteningProjection (leftCoherentTransport p))
      (ULift.up (nerveVertex c))) _⦋0⦌ :=
  ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientRelativeEvaluation s) c v).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _
      (s.toStrictTransportComparisonSpan.coherentSource ≫
        s.toStrictTransportComparisonSpan.coherentComparison.hom)
      (by rw [Category.assoc, s.toStrictTransportComparisonSpan.coherentComparison.over,
        s.toStrictTransportComparisonSpan.coherentSource_over]))

/-- 同じ係数点の weighted 脚による、同じ底の実 fiber 点。 -/
def coefficientWeightedFiberPoint (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (vertexFiber (leftUnstraighteningProjection (leftCoherentTransport p))
      (ULift.up (nerveVertex c))) _⦋0⦌ :=
  ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientRelativeEvaluation s) c v).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _ s.toStrictTransportComparisonSpan.coherentTarget
      s.toStrictTransportComparisonSpan.coherentTarget_over)

/-- 元の係数点の source と weighted 像は、底を固定した同じ fiber 内で同型。 -/
def coefficientFiberPointIso (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    VertexIso (s.coefficientSourceFiberPoint c v) (s.coefficientWeightedFiberPoint c v) :=
  VertexIso.map s.toStrictTransportComparisonSpan.coherentComparison.triangle
    ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientRelativeEvaluation s) c v)

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration

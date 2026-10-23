module
public import SerrePositivity.KST.Fibration.ScaffoldTransportRestriction
public import SerrePositivity.InfinityCategories.F1.Scaffold.UniversalScaffoldFiber

/-! # strict transport の元の係数値での、同じ scaffold 三角の制限 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace ScaffoldTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : ScaffoldTransportComparisonSpan p)

/-- 元の係数値の定値包含を用いて、同じ scaffold 三角を制限する。 -/
def coefficientTriangle (c : I) : FunctorIso
    ((SSet.uliftFunctor.{u + 1, u}).map
      (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)) ≫
        s.toStrictTransportComparisonSpan.coherentComparison.hom)
    ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
        leftCoherentTransportComparison p) := by
  have h := (s.scaffoldTriangle).precomp ((SSet.uliftFunctor.{u + 1, u}).map
    (simplicialReplacementConstantLift (leftStrictTransportDiagram p) c))
  rw [← Category.assoc, ← Functor.map_comp,
    simplicialReplacementConstantLift_universalScaffold, ← Category.assoc, ← Functor.map_comp,
    simplicialReplacementConstantLift_tautScaffold] at h
  exact h

/-- 元の係数点を評価した三角。source は元の恒等射評価であり、任意の同値に置換しない。 -/
def coefficientPointIso (c : I) (v : (leftStrictTransport p c) _⦋0⦌) : VertexIso
    (((SSet.uliftFunctor.{u + 1, u}).map
      (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)) ≫
        s.toStrictTransportComparisonSpan.coherentComparison.hom).app
          (Opposite.op ⦋0⦌) (ULift.up v))
    (((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
        leftCoherentTransportComparison p).app (Opposite.op ⦋0⦌) (ULift.up v)) :=
  (s.coefficientTriangle c).app (ULift.up v)

/-- 元の係数点の同じ三角を pointed-space に送る。 -/
def coefficientPointedIso (c : I) (v : (leftStrictTransport p c) _⦋0⦌) : VertexIso
    (((SSet.uliftFunctor.{u + 1, u}).map
      (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)) ≫
        s.toStrictTransportComparisonSpan.representation.pointedMap).app
          (Opposite.op ⦋0⦌) (ULift.up v))
    (((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
        leftCoherentTransportComparison p ≫
          pullback.fst pointedSpaceProjection (leftCoherentTransport p)).app
            (Opposite.op ⦋0⦌) (ULift.up v)) :=
  VertexIso.map (s.coefficientPointIso c v)
    (pullback.fst pointedSpaceProjection (leftCoherentTransport p))

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration

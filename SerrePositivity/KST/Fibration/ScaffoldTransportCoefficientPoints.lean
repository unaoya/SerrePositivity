module
public import SerrePositivity.KST.Fibration.ScaffoldTransportCoefficientFiber
public import SerrePositivity.KST.Fibration.RelativeFunctorEvaluationVertex

/-! # 同じ相対三角の係数 fiber 点は、元の恒等射評価と weighted 包含を回収する -/

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

/-- 元の係数値上の source 脚は、元の恒等射評価そのもの。 -/
theorem coefficientEmbedding_source (c : I) :
    s.coefficientEmbedding c ≫ s.toStrictTransportComparisonSpan.coherentSource =
      (SSet.uliftFunctor.{u + 1, u}).map
        (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)) := by
  rw [coefficientEmbedding, StrictTransportComparisonSpan.coherentSource,
    ← Functor.map_comp, Category.assoc, s.source_restriction,
    simplicialReplacementConstantLift_universalScaffold]

/-- 元の係数値上の weighted 脚は、同じ定値包含と同じ coherent 比較を通る。 -/
theorem coefficientEmbedding_target (c : I) :
    s.coefficientEmbedding c ≫ s.toStrictTransportComparisonSpan.coherentTarget =
      (SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
          leftCoherentTransportComparison p := by
  rw [coefficientEmbedding, StrictTransportComparisonSpan.coherentTarget,
    ← Category.assoc, ← Functor.map_comp, Category.assoc, s.weighted_restriction,
    simplicialReplacementConstantLift_tautScaffold]

/-- 同じ相対三角の source fiber 点の全空間の値を回収する。 -/
theorem coefficientSourceFiberPoint_val (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (s.coefficientSourceFiberPoint c v).val =
      (((SSet.uliftFunctor.{u + 1, u}).map
        (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)) ≫
          s.toStrictTransportComparisonSpan.coherentComparison.hom).app
            (Opposite.op ⦋0⦌) (ULift.up v)) := by
  have hv := relativeFunctorOverPre_evaluate_val
    (leftUnstraighteningProjection (leftCoherentTransport p))
    s.toStrictTransportComparisonSpan.coherentBase (coefficientBase (p := p) c)
    (s.coefficientEmbedding c) (s.coefficientEmbedding_over c)
    (s.toStrictTransportComparisonSpan.coherentSource ≫
      s.toStrictTransportComparisonSpan.coherentComparison.hom)
    (by rw [Category.assoc, s.toStrictTransportComparisonSpan.coherentComparison.over,
      s.toStrictTransportComparisonSpan.coherentSource_over]) (ULift.up v)
  have hm : s.coefficientEmbedding c ≫
      (s.toStrictTransportComparisonSpan.coherentSource ≫
        s.toStrictTransportComparisonSpan.coherentComparison.hom) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)) ≫
          s.toStrictTransportComparisonSpan.coherentComparison.hom := by
    rw [← Category.assoc, s.coefficientEmbedding_source]
  exact hv.trans (congrArg (fun f => f.app (Opposite.op ⦋0⦌) (ULift.up v)) hm)

/-- 同じ相対三角の weighted fiber 点の全空間の値を回収する。 -/
theorem coefficientWeightedFiberPoint_val (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (s.coefficientWeightedFiberPoint c v).val =
      (((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
          leftCoherentTransportComparison p).app (Opposite.op ⦋0⦌) (ULift.up v)) := by
  have hv := relativeFunctorOverPre_evaluate_val
    (leftUnstraighteningProjection (leftCoherentTransport p))
    s.toStrictTransportComparisonSpan.coherentBase (coefficientBase (p := p) c)
    (s.coefficientEmbedding c) (s.coefficientEmbedding_over c)
    s.toStrictTransportComparisonSpan.coherentTarget
    s.toStrictTransportComparisonSpan.coherentTarget_over (ULift.up v)
  exact hv.trans (congrArg (fun f => f.app (Opposite.op ⦋0⦌) (ULift.up v))
    (s.coefficientEmbedding_target c))

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration

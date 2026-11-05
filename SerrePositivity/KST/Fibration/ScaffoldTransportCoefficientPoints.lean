module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportCoefficientPoints
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
  {p : E ⟶ nerve I} [LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan p)

/-- 同じ相対三角の source fiber 点の全空間の値を回収する。 -/
theorem coefficientSourceFiberPoint_val (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (s.coefficientSourceFiberPoint c v).val =
      (((SSet.uliftFunctor.{u + 1, u}).map
        (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)) ≫
          s.toStrictTransportComparisonSpan.coherentComparison.hom).app
            (Opposite.op ⦋0⦌) (ULift.up v)) := by
  have hv := relativeFunctorOverPre_evaluate_val
    (leftUnstraighteningProjection (leftCoherentTransport p))
    s.toStrictTransportComparisonSpan.coherentBase (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientBase (p := p) c)
    ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding s) c) ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding_over s) c)
    (s.toStrictTransportComparisonSpan.coherentSource ≫
      s.toStrictTransportComparisonSpan.coherentComparison.hom)
    (by rw [Category.assoc, s.toStrictTransportComparisonSpan.coherentComparison.over,
      s.toStrictTransportComparisonSpan.coherentSource_over]) (ULift.up v)
  have hm : (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding s) c ≫
      (s.toStrictTransportComparisonSpan.coherentSource ≫
        s.toStrictTransportComparisonSpan.coherentComparison.hom) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)) ≫
          s.toStrictTransportComparisonSpan.coherentComparison.hom := by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding_source s)]
  exact hv.trans (congrArg (fun f => f.app (Opposite.op ⦋0⦌) (ULift.up v)) hm)

/-- 同じ相対三角の weighted fiber 点の全空間の値を回収する。 -/
theorem coefficientWeightedFiberPoint_val (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (s.coefficientWeightedFiberPoint c v).val =
      (((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
          leftCoherentTransportComparison p).app (Opposite.op ⦋0⦌) (ULift.up v)) := by
  have hv := relativeFunctorOverPre_evaluate_val
    (leftUnstraighteningProjection (leftCoherentTransport p))
    s.toStrictTransportComparisonSpan.coherentBase (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientBase (p := p) c)
    ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding s) c) ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding_over s) c)
    s.toStrictTransportComparisonSpan.coherentTarget
    s.toStrictTransportComparisonSpan.coherentTarget_over (ULift.up v)
  exact hv.trans (congrArg (fun f => f.app (Opposite.op ⦋0⦌) (ULift.up v))
    ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding_target s) c))

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration

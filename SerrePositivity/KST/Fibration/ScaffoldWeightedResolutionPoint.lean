module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldWeightedResolutionPoint
import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldWeightedResolutionPoint
public import SerrePositivity.KST.Fibration.ScaffoldTransportPointedCoefficient
public import SerrePositivity.KST.Fibration.OppositeKanResolutionEvaluation

/-! # 元の scaffold の同じ weighted 点を既存の左解像比較へ厳密に戻す -/

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

/-- 元の weighted 射の係数作用を、元の図式を明記して左解像比較へ戻す。 -/
theorem coherentComparison_constant_resolution (c : I) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
        leftCoherentTransportComparison p ≫
          CategoryTheory.Limits.pullback.fst pointedSpaceProjection (leftCoherentTransport p) =
    pointedSpaceLeftResolutionComparison ((leftStrictTransportFunctor p).obj c) ≫
      vertexFiberι pointedSpaceProjection
        (spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj c))) := by
  have h := oppositeKanUnstraighteningComparison_constant_resolution
    (leftStrictTransportFunctor p) c
  simpa only [leftCoherentTransportComparison, leftCoherentTransport,
    leftStrictTransportFunctor, kanObjectForget, leftStrictTransportDiagram, Functor.comp] using h

/-- 分類値を元の反転 Kan 空間の標準頂点へ同じ等号で移した weighted 点。 -/
def coefficientWeightedResolutionPoint (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (vertexFiber pointedSpaceProjection
      (spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj c))))
        _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Stable.Transport.vertexFiberPointReindex pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) c) (s.coefficientWeightedPointedFiberPoint c v)

/-- 同じ weighted 点は、頂点の表示を揃えると左解像比較の元の係数点の実像と一致。 -/
theorem coefficientWeightedResolutionPoint_eq (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    s.coefficientWeightedResolutionPoint c v =
      (pointedSpaceLeftResolutionComparison ((leftStrictTransportFunctor p).obj c)).app
        (Opposite.op ⦋0⦌) (ULift.up v) := by
  apply _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.fiberPoint_ext pointedSpaceProjection
    (spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj c)))
  have h := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up v))
    (coherentComparison_constant_resolution (p := p) c)
  exact (s.coefficientWeightedPointedFiberPoint_val c v).trans h

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration

module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldWeightedResolutionPoint
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldWeightedResolutionPoint
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
  {p : E ⟶ nerve I} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan p)

/-- 元の weighted 射の係数作用を、元の図式を明記して左解像比較へ戻す。 -/
theorem coherentComparison_constant_resolution (c : I) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) c) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransportComparison p ≫
          CategoryTheory.Limits.pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionComparison ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p).obj c) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p).obj c))) := by
  have h := oppositeKanUnstraighteningComparison_constant_resolution
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p) c
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransportComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram, Functor.comp] using h

/-- 分類値を元の反転 Kan 空間の標準頂点へ同じ等号で移した weighted 点。 -/
def coefficientWeightedResolutionPoint (c : I) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport p c) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p).obj c))))
        _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.vertexFiberPointReindex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) c) ((_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientWeightedPointedFiberPoint s) c v)

/-- 同じ weighted 点は、頂点の表示を揃えると左解像比較の元の係数点の実像と一致。 -/
theorem coefficientWeightedResolutionPoint_eq (c : I) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport p c) _⦋0⦌) :
    (_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientWeightedResolutionPoint s) c v =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionComparison ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p).obj c)).app
        (Opposite.op ⦋0⦌) (ULift.up v) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldTransportComparisonSpan.fiberPoint_ext _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p).obj c)))
  have h := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up v))
    (coherentComparison_constant_resolution (p := p) c)
  exact ((_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientWeightedPointedFiberPoint_val s) c v).trans h

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration

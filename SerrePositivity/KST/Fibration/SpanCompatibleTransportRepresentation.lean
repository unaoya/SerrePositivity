module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan
public import SerrePositivity.KST.Fibration.SpanCompatibleComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection

/-! # 指定した復元 span の相対三角を保持する coherent transport 表現 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace StrictTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan p)

/-- 同じ指定 span の二脚を結ぶ相対三角も含めて選んだ、coherent な実比較。 -/
def coherentComparison : SpanCompatibleComparison
    ((SSet.uliftFunctor.{u + 1, u}).map p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p))
    s.coherentBase s.coherentSource s.coherentTarget
    s.coherentSource_over s.coherentTarget_over :=
  spanCompatibleComparison _ _ _ _ _ _ _
    s.coherentSource_equivalence s.coherentTarget_equivalence

/-- 同じ実比較を用いた表現。元の span の三角を別の存在選択で失わない。 -/
def representation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p) where
  diagram := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p
  comparison := (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).hom
  over_base := (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).over
  fiber_equivalence b :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence _ _ _
      (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).over (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).equivalence b

/-- 元の共通全空間の指定点において、同じ相対三角を実 fiber 内で評価する。 -/
def representationPointIso (z : s.total _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p)) s.coherentBase
      (ULift.up z)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex _ _ (s.coherentSource ≫ (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).hom)
          (by rw [Category.assoc, (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).over, s.coherentSource_over])))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p)) s.coherentBase
      (ULift.up z)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex _ _ s.coherentTarget s.coherentTarget_over)) :=
  (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).pointIso (ULift.up z)

end StrictTransportComparisonSpan
end SerrePositivity.KST.Fibration

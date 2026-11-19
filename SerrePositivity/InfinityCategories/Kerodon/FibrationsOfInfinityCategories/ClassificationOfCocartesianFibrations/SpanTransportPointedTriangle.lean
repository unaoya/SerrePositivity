module
public import SerrePositivity.KST.Fibration.SpanCompatibleTransportRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointedFamilyPointHom

/-! # 指定復元 span の同じ三角を元の全空間の点と pointed space で評価する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace StrictTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan p)

/-- 相対三角の元の全空間への像。元の二脚と同じ比較射を使う。 -/
def representationTriangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (s.coherentSource ≫ (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).hom) s.coherentTarget :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).triangle
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj s.total)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.coherentBase))

/-- 元の指定点で同じ三角を評価した全空間の比較。 -/
def representationTotalPointIso (z : s.total _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((s.coherentSource ≫ (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s).hom).app (Opposite.op ⦋0⦌) (ULift.up z))
    (s.coherentTarget.app (Opposite.op ⦋0⦌) (ULift.up z)) := by
  have : InnerFibration s.projection := s.inner
  have : Quasicategory s.total := quasicategory_of_innerFibration s.projection
  exact (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representationTriangle s).app (ULift.up z)

/-- 表現の同じ pointed map と weighted 脚の同じ指定点を結ぶ実比較。 -/
def representationPointedPointIso (z : s.total _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((s.coherentSource ≫ (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representation s).pointedMap).app
      (Opposite.op ⦋0⦌) (ULift.up z))
    ((s.coherentTarget ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p)).app
      (Opposite.op ⦋0⦌) (ULift.up z)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map ((_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representationTotalPointIso s) z)
    (pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p))

/-- 同じ指定点比較の底への作用は、元の点の射を保持する。 -/
theorem representationPointedPointIso_pointHom (z : s.total _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom ((s.coherentSource ≫ (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representation s).pointedMap).app
      (Opposite.op ⦋0⦌) (ULift.up z)) ≫
      (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection).toFunctor.map
        ((_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representationPointedPointIso s) z).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom
      ((s.coherentTarget ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p)).app
        (Opposite.op ⦋0⦌) (ULift.up z)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberPointHom_comp_projection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexFiberPoint ((s.coherentSource ≫ (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representation s).pointedMap).app
      (Opposite.op ⦋0⦌) (ULift.up z)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexFiberPoint
      ((s.coherentTarget ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p)).app
        (Opposite.op ⦋0⦌) (ULift.up z)))
    ((_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representationPointedPointIso s) z).hom
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom ((s.coherentSource ≫ (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representation s).pointedMap).app
    (Opposite.op ⦋0⦌) (ULift.up z)) ≫
      (𝟙 _ ≫ (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection).toFunctor.map
        ((_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representationPointedPointIso s) z).hom ≫ 𝟙 _) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom
      ((s.coherentTarget ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p)).app
        (Opposite.op ⦋0⦌) (ULift.up z)) at h
  simpa only [Category.id_comp, Category.comp_id] using h

end StrictTransportComparisonSpan
end SerrePositivity.KST.Fibration

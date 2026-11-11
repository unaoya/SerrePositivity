module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.StraighteningUnderSectionChart
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.StraighteningUnderSectionChart
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeChartComponents
public import SerrePositivity.KST.Fibration.TransportUnderSectionPoint

/-! # 元の初頂点 under 比較を、同じ切断比較と元の under 制限成分に分解する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w v' w'
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}

/-- 元の初頂点 under 共同同型の二重成分を、同じ under 切断空間へ表示する。 -/
def straighteningFirstVertexUnderChart (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_underIso B)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.doubleFunctorEvaluation (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))) rfl
    (congrArg HomotopyCategory.mk
      (relativeSectionDiagramInfinity_double_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUnderDomains B) X c))

/-- 表示変更後も、元の under 共同同型の同じ指定二重成分を保持する。 -/
theorem straighteningFirstVertexUnderChart_heq_doubleMap
    (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) :
    HEq (straighteningFirstVertexUnderChart X c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_underIso B)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.doubleFunctorEvaluation (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))) := by
  unfold straighteningFirstVertexUnderChart _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.iso_endpoints_heq _ _ _

/-- 同じ元の under 成分は、同じ初頂点の切断比較と同じ実制限成分の合成。 -/
theorem straighteningFirstVertexUnderChart_factor
    (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) :
    straighteningFirstVertexUnderChart X c =
      straighteningFirstVertexSectionChart X c ≪≫ transportUnderJointComponentIso X c := by
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.doubleFunctorEvaluation
    (K := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)))
    (A := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.mapNormalizeComposition (hoFunctor.map T).toFunctor
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUnderJointIso B)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_underIso B) rfl
    (congrArg HomotopyCategory.mk
      (relativeSectionDiagramInfinity_double_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B) X c))
    (congrArg HomotopyCategory.mk
      (relativeSectionDiagramInfinity_double_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUnderDomains B) X c))

/-- 同じ初頂点比較で表示した元の切断点は、元の under 比較で同じ実制限像へ移る。 -/
theorem straighteningFirstVertexUnderChart_pointHom
    (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)
    (v : (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B)).obj c).obj X).obj
      _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B)).obj c).obj X)).symm v) ≫
      (straighteningFirstVertexSectionChart X c).inv ≫
        (straighteningFirstVertexUnderChart X c).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUnderDomains B)).obj c).obj X)).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre X.val.hom
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexUnderDomainTransformation B).app (Opposite.op c))).app
            (Opposite.op ⦋0⦌) v)) := by
  rw [straighteningFirstVertexUnderChart_factor]
  simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
  exact transportUnderJointComponentIso_pointHom X c v

end SerrePositivity.KST.Fibration

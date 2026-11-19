module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldBaseChangeCoefficientNaturality
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldBaseChangeCoefficientNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldBaseChangeLeftPoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldBaseChangeRightPoint

/-! # 元の大域底変換による、同じ切断からの scaffold 復元点の自然性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ単体切断の初頂点 fiber 点の、実 scaffold 復元射による像。 -/
def scaffoldReconstructionSectionPoint {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).obj (Opposite.op c)).hom) _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallUnstraighteningPointedImage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p))
      (scaffoldPointedReconstruction p) (scaffoldPointedReconstruction_projection p)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).app
        (Opposite.op ⦋0⦌) (firstVertexSectionFiberPoint p c v))

variable {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  [Quasicategory B] (k : D ⟶ B) [Quasicategory D]

/-- 元の大域底変換の指定成分を、両側の同じ実図式値で表示する。 -/
def scaffoldBaseChangeCoefficientIso (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory D) :=
  eqToIso (congrArg HomotopyCategory.mk
    (firstVertexDiagram_source_vertex p ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k).obj c))) ≪≫
  (eqToIso (congrArg HomotopyCategory.mk
    (straighteningBaseChangeLeft_source_vertex k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p) c))).symm ≪≫
  straighteningGlobalBaseChangeValueIso k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p) c ≪≫
  eqToIso (congrArg HomotopyCategory.mk
    (straighteningBaseChangeRight_source_vertex k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p) c)) ≪≫
  (eqToIso (congrArg HomotopyCategory.mk
    (firstVertexDiagram_source_vertex (pullback.snd p k) c))).symm

omit [Quasicategory B] [Quasicategory D] in
/-- 表示変更に用いたのは端点の等式だけで、元の実図式の指定成分を保持する。 -/
theorem scaffoldBaseChangeCoefficientIso_heq_diagramValue
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory D) :
    HEq (scaffoldBaseChangeCoefficientIso p k c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap D).app
          (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))))) := by
  have h : HEq (scaffoldBaseChangeCoefficientIso p k c)
      (straighteningGlobalBaseChangeValueIso k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p) c) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.endpointSpan_heq _ _ _ _ _
  exact h.trans (leftStraighteningDiagramBaseChange_heq_globalValue k p c).symm

/-- 同じ pullback 切断の第一射影から得る元の底の復元点は、
元の大域底変換の同じ指定成分によって pullback 側の復元点へ送られる。 -/
theorem scaffoldBaseChangeCoefficientIso_pointHom (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory D)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd p k)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor D).obj (Opposite.op c)).hom) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionSectionPoint p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k).obj c)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.straighteningBaseChangeImageSectionPoint p k c
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app
            (Opposite.op ⦋0⦌) v))) ≫
      (scaffoldBaseChangeCoefficientIso p k c).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionSectionPoint (pullback.snd p k) c v) := by
  have hl := scaffoldBaseChangeLeftChart_pointHom p k c
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app (Opposite.op ⦋0⦌) v)
  have hr := scaffoldGlobalBaseChange_pullback_pointHom p k c v
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.pointTriangle _ _ _ _ _ _ _ _ _ hl hr

end SerrePositivity.KST.Fibration

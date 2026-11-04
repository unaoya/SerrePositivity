module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldBaseChangeCoefficientNaturality
public import SerrePositivity.KST.Fibration.ScaffoldBaseChangeLeftPoint
public import SerrePositivity.KST.Fibration.ScaffoldBaseChangeRightPoint

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
    (p : E ⟶ B) [LeftFibration p] (c : TransportSimplexCategory B)
    (v : (relativeFunctorSpace p
      ((transportSimplexDomainFunctor B).obj (Opposite.op c)).hom) _⦋0⦌) :=
  smallUnstraighteningPointedImage (leftStraighteningInfinityDiagram p)
    ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))
    ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
      (scaffoldPointedReconstruction p) (scaffoldPointedReconstruction_projection p)
      ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))).app
        (Opposite.op ⦋0⦌) (firstVertexSectionFiberPoint p c v))

variable {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  [Quasicategory B] (k : D ⟶ B) [Quasicategory D]

/-- 元の大域底変換の指定成分を、両側の同じ実図式値で表示する。 -/
def scaffoldBaseChangeCoefficientIso (c : TransportSimplexCategory D) :=
  eqToIso (congrArg HomotopyCategory.mk
    (firstVertexDiagram_source_vertex p ((transportSimplexFunctor k).obj c))) ≪≫
  (eqToIso (congrArg HomotopyCategory.mk
    (straighteningBaseChangeLeft_source_vertex k (leftFibrationObjectOf p) c))).symm ≪≫
  straighteningGlobalBaseChangeValueIso k (leftFibrationObjectOf p) c ≪≫
  eqToIso (congrArg HomotopyCategory.mk
    (straighteningBaseChangeRight_source_vertex k (leftFibrationObjectOf p) c)) ≪≫
  (eqToIso (congrArg HomotopyCategory.mk
    (firstVertexDiagram_source_vertex (pullback.snd p k) c))).symm

omit [Quasicategory B] [Quasicategory D] in
/-- 表示変更に用いたのは端点の等式だけで、元の実図式の指定成分を保持する。 -/
theorem scaffoldBaseChangeCoefficientIso_heq_diagramValue
    (c : TransportSimplexCategory D) :
    HEq (scaffoldBaseChangeCoefficientIso p k c)
      (VertexIso.map (leftStraighteningInfinityDiagram_baseChangeIso p k)
        (evaluateFunctorAt (ULift.up ((transportSimplexFirstVertexMap D).app
          (Opposite.op ⦋0⦌) (nerveVertex c))))) := by
  have h : HEq (scaffoldBaseChangeCoefficientIso p k c)
      (straighteningGlobalBaseChangeValueIso k (leftFibrationObjectOf p) c) :=
    endpointSpan_heq _ _ _ _ _
  exact h.trans (leftStraighteningDiagramBaseChange_heq_globalValue k p c).symm

/-- 同じ pullback 切断の第一射影から得る元の底の復元点は、
元の大域底変換の同じ指定成分によって pullback 側の復元点へ送られる。 -/
theorem scaffoldBaseChangeCoefficientIso_pointHom (c : TransportSimplexCategory D)
    (v : (relativeFunctorSpace (pullback.snd p k)
      ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom) _⦋0⦌) :
    cosliceFiberPointHom (scaffoldReconstructionSectionPoint p
      ((transportSimplexFunctor k).obj c)
      (straighteningBaseChangeImageSectionPoint p k c
        ((relativeFunctorBaseChangeForward p k
          ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app
            (Opposite.op ⦋0⦌) v))) ≫
      (scaffoldBaseChangeCoefficientIso p k c).hom =
    cosliceFiberPointHom (scaffoldReconstructionSectionPoint (pullback.snd p k) c v) := by
  have hl := scaffoldBaseChangeLeftChart_pointHom p k c
    ((relativeFunctorBaseChangeForward p k
      ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app (Opposite.op ⦋0⦌) v)
  have hr := scaffoldGlobalBaseChange_pullback_pointHom p k c v
  exact pointTriangle _ _ _ _ _ _ _ _ _ hl hr

end SerrePositivity.KST.Fibration

module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldGlobalCoefficientPoint
public import SerrePositivity.KST.Fibration.FirstVertexSectionFiber
public import SerrePositivity.KST.Fibration.ScaffoldStraighteningValue

/-! # 降下後の同じ scaffold 比較は、元の初頂点 fiber の同じ実点を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
  (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))

/-- 降下後の元の指定成分は、元の初頂点 fiber の同じ点の pointedMap 像を回収する。 -/
theorem scaffoldStraighteningGlobalChart_original_pointHom (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
      (leftFibrationObjectOf p)).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
        (leftFibrationObjectOf p))).symm v) ≫
      (straighteningFirstVertexSectionChart (leftFibrationObjectOf p) c).inv ≫
        (scaffoldStraighteningGlobalChart p R c).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((transportRepresentationPointedFiberMap R
      (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
        (nerveVertex c)))).app (Opposite.op ⦋0⦌)
        ((uliftVertexFiberIso p ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
          (nerveVertex c))).hom.app (Opposite.op ⦋0⦌)
          (ULift.up (firstVertexSectionFiberPoint p c v)))) := by
  have hp := scaffoldStraighteningGlobalChart_pointHom p R c v
  have hf := nativeRestrict_firstVertex_point p c R
    ((leftStrictTransportEvaluate (pullback.snd p (transportSimplexFirstVertexMap B)) c).app
      (Opposite.op ⦋0⦌) ((firstVertexStrictSectionMap p c).app (Opposite.op ⦋0⦌) v))
  exact hp.trans (congrArg _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom hf)

/-- native 表現では、元の同じ native fiber 写像の点を回収する。 -/
theorem scaffoldStraighteningGlobalChart_native_pointHom (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
      (leftFibrationObjectOf p)).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
        (leftFibrationObjectOf p))).symm v) ≫
      (straighteningFirstVertexSectionChart (leftFibrationObjectOf p) c).inv ≫
        (scaffoldStraighteningGlobalChart p (nativeLeftTransportRepresentation p) c).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((nativeTransportPointedFiberMap p
      ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))).app
        (Opposite.op ⦋0⦌) (ULift.up (firstVertexSectionFiberPoint p c v))) :=
  scaffoldStraighteningGlobalChart_original_pointHom p (nativeLeftTransportRepresentation p) c v

end SerrePositivity.KST.Fibration

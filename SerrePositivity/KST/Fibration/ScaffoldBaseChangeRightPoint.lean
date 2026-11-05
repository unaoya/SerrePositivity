module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldBaseChangeRightPoint
import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldBaseChangeRightPoint
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeRightEndpoints
public import SerrePositivity.KST.Fibration.ScaffoldReconstructionCoefficientPoint
public import SerrePositivity.KST.Fibration.StraighteningGlobalBaseChangeValue

/-! # 元の大域底変換の指定切断像を、pullback の同じ scaffold 復元点へ接続する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (k : D ⟶ B) [Quasicategory D]

/-- 右側の元の切断比較は、端点輸送後に同じ fiber 点の復元像を回収する。 -/
theorem scaffoldBaseChangeRightChart_pointHom (c : TransportSimplexCategory D)
    (v : (relativeFunctorSpace (pullback.snd p k)
      ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).obj c).obj
        (leftFibrationBaseChangeObject k (leftFibrationObjectOf p)))).symm v) ≫
      (straighteningBaseChangeRightChart k (leftFibrationObjectOf p) c).inv ≫
        (eqToIso (congrArg HomotopyCategory.mk
          (straighteningBaseChangeRight_source_vertex k (leftFibrationObjectOf p) c))).hom ≫
        (eqToIso (congrArg HomotopyCategory.mk
          (firstVertexDiagram_source_vertex (pullback.snd p k) c))).inv =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram (pullback.snd p k))
      ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌) (nerveVertex c))
      ((vertexFiberMap (pullback.snd p k)
        (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram (pullback.snd p k)))
        (scaffoldPointedReconstruction (pullback.snd p k))
        (scaffoldPointedReconstruction_projection (pullback.snd p k))
        ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌) (nerveVertex c))).app
          (Opposite.op ⦋0⦌) (firstVertexSectionFiberPoint (pullback.snd p k) c v))) := by
  have h := scaffoldPointedReconstruction_coefficient_pointHom (pullback.snd p k) c v
  have hc : F2.isoNormalizeEndpoints
      (straighteningBaseChangeRightChart k (leftFibrationObjectOf p) c)
      (congrArg HomotopyCategory.mk
        (straighteningBaseChangeRight_source_vertex k (leftFibrationObjectOf p) c)) rfl =
      straighteningFirstVertexSectionChart (leftFibrationObjectOf (pullback.snd p k)) c :=
    straighteningBaseChangeRightChart_eq_firstVertex k (leftFibrationObjectOf p) c
  have hn := _root_.SerrePositivity.InfinityCategories.Stable.Transport.point_normalize_inv
    (straighteningBaseChangeRightChart k (leftFibrationObjectOf p) c)
    (congrArg HomotopyCategory.mk
      (straighteningBaseChangeRight_source_vertex k (leftFibrationObjectOf p) c))
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).obj c).obj
        (leftFibrationBaseChangeObject k (leftFibrationObjectOf p)))).symm v))
    (eqToIso (congrArg HomotopyCategory.mk
      (firstVertexDiagram_source_vertex (pullback.snd p k) c))).inv
  rw [hc] at hn
  exact hn.trans h

/-- 元の大域底変換は、同じ切断から得る pullback 復元点を回収する。 -/
theorem scaffoldGlobalBaseChange_pullback_pointHom (c : TransportSimplexCategory D)
    (v : (relativeFunctorSpace (pullback.snd p k)
      ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram
        (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj
          (leftFibrationObjectOf p))).symm
        ((relativeFunctorBaseChangeForward p k
          ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app
            (Opposite.op ⦋0⦌) v)) ≫
      (straighteningBaseChangeLeftChart k (leftFibrationObjectOf p) c).inv ≫
      (straighteningGlobalBaseChangeValueIso k (leftFibrationObjectOf p) c).hom ≫
        (eqToIso (congrArg HomotopyCategory.mk
          (straighteningBaseChangeRight_source_vertex k (leftFibrationObjectOf p) c))).hom ≫
        (eqToIso (congrArg HomotopyCategory.mk
          (firstVertexDiagram_source_vertex (pullback.snd p k) c))).inv =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram (pullback.snd p k))
      ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌) (nerveVertex c))
      ((vertexFiberMap (pullback.snd p k)
        (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram (pullback.snd p k)))
        (scaffoldPointedReconstruction (pullback.snd p k))
        (scaffoldPointedReconstruction_projection (pullback.snd p k))
        ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌) (nerveVertex c))).app
          (Opposite.op ⦋0⦌) (firstVertexSectionFiberPoint (pullback.snd p k) c v))) := by
  have h := straighteningGlobalBaseChangeValueIso_pointHom k (leftFibrationObjectOf p) c v
  exact (_root_.SerrePositivity.InfinityCategories.Stable.Transport.appendPointTriangle _ _ _ _ _ _ _ h).trans
    (scaffoldBaseChangeRightChart_pointHom p k c v)

end SerrePositivity.KST.Fibration

module
public import SerrePositivity.KST.Fibration.ScaffoldReconstructionCoefficientPoint
public import SerrePositivity.KST.Fibration.FirstVertexDiagramVertices
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldBaseChangeLeftPoint
import all SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldBaseChangeLeftPoint
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeLeftEndpoints
public import SerrePositivity.InfinityCategories.F1.Transport.PointedSpaceEqualityTransport

/-! # 像の単体へ輸送した同じ切断点を、元の底側の scaffold 復元像へ接続する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

variable {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] [Quasicategory B]
  (k : D ⟶ B)

/-- 左の元の切断比較は、輸送した同じ切断点の初頂点 fiber の復元像を回収する。 -/
theorem scaffoldBaseChangeLeftChart_pointHom (c : TransportSimplexCategory D)
    (v : (((relativeSectionEnrichedDiagram
      (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj
        (leftFibrationObjectOf p)).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram
        (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj
          (leftFibrationObjectOf p))).symm v) ≫
      (straighteningBaseChangeLeftChart k (leftFibrationObjectOf p) c).inv ≫
        (eqToIso (congrArg HomotopyCategory.mk
          (straighteningBaseChangeLeft_source_vertex k (leftFibrationObjectOf p) c))).hom ≫
        (eqToIso (congrArg HomotopyCategory.mk
          (firstVertexDiagram_source_vertex p ((transportSimplexFunctor k).obj c)))).inv =
    cosliceFiberPointHom (smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram p)
      ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
        (nerveVertex ((transportSimplexFunctor k).obj c)))
      ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
        (scaffoldPointedReconstruction p) (scaffoldPointedReconstruction_projection p)
        ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
          (nerveVertex ((transportSimplexFunctor k).obj c)))).app (Opposite.op ⦋0⦌)
            (firstVertexSectionFiberPoint p ((transportSimplexFunctor k).obj c)
              (straighteningBaseChangeImageSectionPoint p k c v)))) := by
  have hp := pointedSpaceFiberPointHom_eq_transport
    (straighteningBaseChangeLeft_section_eq k (leftFibrationObjectOf p) c) v
  have hn := point_normalize_both_inv
    (straighteningBaseChangeLeftChart k (leftFibrationObjectOf p) c)
    (congrArg HomotopyCategory.mk
      (straighteningBaseChangeLeft_source_vertex k (leftFibrationObjectOf p) c))
    (congrArg HomotopyCategory.mk (congrArg spaceInfinityVertex
      (straighteningBaseChangeLeft_section_eq k (leftFibrationObjectOf p) c)))
    _ _ (eqToIso (congrArg HomotopyCategory.mk
      (firstVertexDiagram_source_vertex p ((transportSimplexFunctor k).obj c)))).inv hp
  rw [straighteningBaseChangeLeftChart_eq_firstVertex] at hn
  exact hn.trans (scaffoldPointedReconstruction_coefficient_pointHom p
    ((transportSimplexFunctor k).obj c) (straighteningBaseChangeImageSectionPoint p k c v))

end SerrePositivity.KST.Fibration

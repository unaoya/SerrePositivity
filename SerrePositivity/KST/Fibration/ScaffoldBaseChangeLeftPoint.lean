module
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeLeftEndpoints
public import SerrePositivity.KST.Fibration.PointedSpaceEqualityTransport

/-! # 像の単体へ輸送した同じ切断点を、元の底側の scaffold 復元像へ接続する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

private lemma point_normalize_both_inv {C : Type*} [Category C] {a b a' b' z t : C}
    (e : a ≅ b) (hs : a = a') (ht : b = b') (v : z ⟶ b) (w : z ⟶ b')
    (f : a' ⟶ t) (hp : v ≫ (eqToIso ht).hom = w) :
    v ≫ e.inv ≫ (eqToIso hs).hom ≫ f =
      w ≫ (F2.isoNormalizeEndpoints e hs ht).inv ≫ f := by
  rw [← hp]
  simp only [F2.isoNormalizeEndpoints, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc]

variable {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] [Quasicategory B]
  (k : D ⟶ B)

/-- 同じ相対切断の点を、像の単体での切断 Kan 対象へ等式で輸送する。 -/
def straighteningBaseChangeImageSectionPoint (c : TransportSimplexCategory D)
    (v : (((relativeSectionEnrichedDiagram
      (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj
        (leftFibrationObjectOf p)).obj _⦋0⦌) :=
  Eq.mp (congrArg (fun T : KanObject.{u} => T.obj _⦋0⦌)
    (straighteningBaseChangeLeft_section_eq k (leftFibrationObjectOf p) c)) v

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

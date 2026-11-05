module
public import SerrePositivity.KST.Fibration.ScaffoldGlobalCoefficientPoint
public import SerrePositivity.KST.Fibration.ScaffoldPointedReconstruction

/-! # 元の単体切断の指定点を、同じ scaffold 復元射の実 fiber 像へ接続する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]

/-- 元の切断点の指定分類像は、同じ初頂点 fiber 点の scaffold 復元射による実像。 -/
theorem scaffoldPointedReconstruction_coefficient_pointHom (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
      (leftFibrationObjectOf p)).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
        (leftFibrationObjectOf p))).symm v) ≫
      (straighteningFirstVertexSectionChart (leftFibrationObjectOf p) c).inv ≫
        (eqToIso (congrArg HomotopyCategory.mk (firstVertexDiagram_source_vertex p c))).inv =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram p)
      ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))
      ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
        (scaffoldPointedReconstruction p) (scaffoldPointedReconstruction_projection p)
        ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))).app
          (Opposite.op ⦋0⦌) (firstVertexSectionFiberPoint p c v))) := by
  let b := (transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c)
  let w := firstVertexSectionFiberPoint p c v
  let e := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue
    (scaffoldStraighteningRepresentationIso p (nativeLeftTransportRepresentation p)) (ULift.up b)
  let C := eqToIso (congrArg HomotopyCategory.mk (firstVertexDiagram_source_vertex p c))
  let x := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
    (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj
      (leftFibrationObjectOf p))).symm v) ≫
        (straighteningFirstVertexSectionChart (leftFibrationObjectOf p) c).inv ≫ C.inv
  let n := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((nativeTransportPointedFiberMap p b).app
    (Opposite.op ⦋0⦌) (ULift.up w))
  have hf : x ≫ e.hom = n := by
    have h := scaffoldStraighteningGlobalChart_native_pointHom p c v
    simp only [scaffoldStraighteningGlobalChart, F2.isoNormalizeEndpoints, Iso.trans_hom,
      Iso.symm_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id] at h
    dsimp only [x]
    simp only [Category.assoc]
    exact h
  have hi : x = n ≫ e.inv := ((Iso.comp_inv_eq e).2 hf.symm).symm
  have hr := scaffoldPointedReconstruction_pointHom p b w
  rw [nativeLeftTransportComparison_pointedImage p b w] at hr
  have he := congrArg (fun m => n ≫ m)
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_inv (scaffoldStraighteningRepresentationIso p
      (nativeLeftTransportRepresentation p)) (ULift.up b))
  exact hi.trans (he.trans hr)

end SerrePositivity.KST.Fibration

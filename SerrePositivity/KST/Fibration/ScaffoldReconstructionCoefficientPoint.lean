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
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]

/-- 元の切断点の指定分類像は、同じ初頂点 fiber 点の scaffold 復元射による実像。 -/
theorem scaffoldPointedReconstruction_coefficient_pointHom (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)
    (v : (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B)).obj c).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p)).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B)).obj c).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p))).symm v) ≫
      (straighteningFirstVertexSectionChart (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p) c).inv ≫
        (eqToIso (congrArg HomotopyCategory.mk (firstVertexDiagram_source_vertex p c))).inv =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallUnstraighteningPointedImage
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p))
        (scaffoldPointedReconstruction p) (scaffoldPointedReconstruction_projection p)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).app
          (Opposite.op ⦋0⦌) (firstVertexSectionFiberPoint p c v))) := by
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)
  let w := firstVertexSectionFiberPoint p c v
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIsoValue
    (scaffoldStraighteningRepresentationIso p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nativeLeftTransportRepresentation p)) (ULift.up b)
  let C := eqToIso (congrArg HomotopyCategory.mk (firstVertexDiagram_source_vertex p c))
  let x := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B)).obj c).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p))).symm v) ≫
        (straighteningFirstVertexSectionChart (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p) c).inv ≫ C.inv
  let n := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((nativeTransportPointedFiberMap p b).app
    (Opposite.op ⦋0⦌) (ULift.up w))
  have hf : x ≫ e.hom = n := by
    have h := scaffoldStraighteningGlobalChart_native_pointHom p c v
    simp only [scaffoldStraighteningGlobalChart, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints, Iso.trans_hom,
      Iso.symm_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id] at h
    dsimp only [x]
    simp only [Category.assoc]
    exact h
  have hi : x = n ≫ e.inv := ((Iso.comp_inv_eq e).2 hf.symm).symm
  have hr := scaffoldPointedReconstruction_pointHom p b w
  rw [nativeLeftTransportComparison_pointedImage p b w] at hr
  have he := congrArg (fun m => n ≫ m)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIsoValue_inv (scaffoldStraighteningRepresentationIso p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nativeLeftTransportRepresentation p)) (ULift.up b))
  exact hi.trans (he.trans hr)

end SerrePositivity.KST.Fibration

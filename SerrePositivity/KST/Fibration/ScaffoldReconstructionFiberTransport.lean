module
public import SerrePositivity.KST.Fibration.ScaffoldReconstructionFiberPoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.CosliceTransportPointHom
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso

/-! # 同じ復元の実 fiber 点の等式輸送と頂点同型は、指定分類射に反映される -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]

/-- 底頂点を等式で揃えた同じ実点の分類射は、元の値の等式同型による後合成。 -/
theorem scaffoldReconstructionFiberPoint_eqToHom_transport {b b' : B _⦋0⦌}
    (h : b = b') (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b w) ≫
      (eqToIso (congrArg (fun z => HomotopyCategory.mk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up z))) h)).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b'
      ((eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h)).app (Opposite.op ⦋0⦌) w)) := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, eqToHom_refl]
  rfl

/-- 同じ実 fiber 内の頂点同型は、同じ復元像の点の分類射の等式を与える。 -/
theorem scaffoldReconstructionFiberPoint_pointHom_eq_of_vertexIso (b : B _⦋0⦌)
    {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso v w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b v) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b w) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p
  let M := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F)
    (scaffoldPointedReconstruction p) (scaffoldPointedReconstruction_projection p) b
  let h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.uliftVertexIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e M)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom_eq_of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map h
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberIso F b).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso F (ULift.up b)).hom))

end SerrePositivity.KST.Fibration

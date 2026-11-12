module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CartesianPrismOpposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.EdgeTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CartesianInitialBoundary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibrationComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexFiberOpposite

/-!
概要：元の終点 fiber から始点 fiber への Cartesian transport と輸送 prism を構成する。
方針：反対圏の cocartesian transport を、fiber の反転同型と二重反転で元へ戻す。
規約：元の底の辺と両端を保持する。使われ方：Quillen cf 対応圏の右導来関手。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
noncomputable section

/-- 指定した辺に沿う、終点 fiber から始点 fiber への Cartesian transport。 -/
def cartesianEdgeTransport {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cartesianFibration_op_toCocartesianHornFibration p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianHornFibration_toCocartesianFibration (SSet.opFunctor.map p)
  let T : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).op ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a).op :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport (SSet.opFunctor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p a).inv
  exact (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)).inv ≫
    SSet.opFunctor.map T ≫ (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)).hom

/-- 同じ輸送は、両端・底の辺・全垂直辺の Cartesian 性を保持した prism を持つ。 -/
lemma cartesianEdgeTransport_witness {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ E,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = cartesianEdgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ∧
      H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e.edge ∧
      ∀ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cartesianFibration_op_toCocartesianHornFibration p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianHornFibration_toCocartesianFibration (SSet.opFunctor.map p)
  obtain ⟨H, h0, h1, hb, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport (SSet.opFunctor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)
  let K := ((Δ[1] : SSet.{u}) ◁ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p b).hom) ≫ H
  have hk0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ K = SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
    exact congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ⟶
      E.op ↦ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p b).hom ≫ f) h0
  have hk1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ K =
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p b).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport (SSet.opFunctor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p a).inv) ≫
          SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a) := by
    exact congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ⟶
      E.op ↦ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p b).hom ≫ f) h1
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism K, ?_, ?_, ?_, ?_⟩
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism_endpoint]
    change (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ K) ≫ _ = _
    rw [hk1, Functor.map_comp]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism_endpoint]
    change (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ K) ≫ _ = _
    rw [hk0]
    rfl
  · have hkb : K ≫ SSet.opFunctor.map p =
        fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).op ≫
          (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e).edge : (Δ[1] : SSet.{u}) ⟶ B.op) := by
      exact congrArg (fun f : (Δ[1] : SSet.{u}) ⊗
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ⟶ B.op ↦
          ((Δ[1] : SSet.{u}) ◁ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p b).hom) ≫ f) hb
    rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unreversePrism_postcomp, hkb, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unreversePrism_base]
  · apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unreversePrism_vertical_isCartesian p K
    intro v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p)
      (H.app (Opposite.op ⦋1⦌) (_, (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p b).hom.app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    exact hc ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p b).hom.app _ v)

end
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

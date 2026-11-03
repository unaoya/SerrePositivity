module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CartesianPrismOpposite
public import SerrePositivity.InfinityCategories.F1.Transport.EdgeTransport
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CartesianInitialBoundary
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianHornFibrationComparison
public import SerrePositivity.InfinityCategories.Core.VertexFiberOpposite

/-!
概要：元の終点 fiber から始点 fiber への Cartesian transport と輸送 prism を構成する。
方針：反対圏の cocartesian transport を、fiber の反転同型と二重反転で元へ戻す。
規約：元の底の辺と両端を保持する。使われ方：Quillen cf 対応圏の右導来関手。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 指定した辺に沿う、終点 fiber から始点 fiber への Cartesian transport。 -/
def cartesianEdgeTransport {E B : SSet.{u}} (p : E ⟶ B) [CartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b) :
    vertexFiber p b ⟶ vertexFiber p a := by
  have := SerrePositivity.InfinityCategories.F1B.cartesianFibration_op_toCocartesianHornFibration p
  have := SerrePositivity.InfinityCategories.F1B.cocartesianHornFibration_toCocartesianFibration (SSet.opFunctor.map p)
  let T : (vertexFiber p b).op ⟶ (vertexFiber p a).op :=
    (vertexFiberOpIso p b).hom ≫
      edgeTransport (SSet.opFunctor.map p) (edgeOp e) ≫ (vertexFiberOpIso p a).inv
  exact (SSet.opFunctorCompOpFunctorIso.app (vertexFiber p b)).inv ≫
    SSet.opFunctor.map T ≫ (SSet.opFunctorCompOpFunctorIso.app (vertexFiber p a)).hom

/-- 同じ輸送は、両端・底の辺・全垂直辺の Cartesian 性を保持した prism を持つ。 -/
lemma cartesianEdgeTransport_witness {E B : SSet.{u}} (p : E ⟶ B) [CartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p b ⟶ E,
      prismEndpoint 0 _ ≫ H = cartesianEdgeTransport p e ≫ vertexFiberι p a ∧
      prismEndpoint 1 _ ≫ H = vertexFiberι p b ∧
      H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e.edge ∧
      ∀ v : (vertexFiber p b) _⦋0⦌, IsCartesianEdge p
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1)) := by
  have := SerrePositivity.InfinityCategories.F1B.cartesianFibration_op_toCocartesianHornFibration p
  have := SerrePositivity.InfinityCategories.F1B.cocartesianHornFibration_toCocartesianFibration (SSet.opFunctor.map p)
  obtain ⟨H, h0, h1, hb, hc⟩ := edgeTransport_isTransport (SSet.opFunctor.map p) (edgeOp e)
  let K := ((Δ[1] : SSet.{u}) ◁ (vertexFiberOpIso p b).hom) ≫ H
  have hk0 : prismEndpoint 0 _ ≫ K = SSet.opFunctor.map (vertexFiberι p b) := by
    exact congrArg (fun f : vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ⟶
      E.op ↦ (vertexFiberOpIso p b).hom ≫ f) h0
  have hk1 : prismEndpoint 1 _ ≫ K =
      ((vertexFiberOpIso p b).hom ≫
        edgeTransport (SSet.opFunctor.map p) (edgeOp e) ≫ (vertexFiberOpIso p a).inv) ≫
          SSet.opFunctor.map (vertexFiberι p a) := by
    exact congrArg (fun f : vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ⟶
      E.op ↦ (vertexFiberOpIso p b).hom ≫ f) h1
  refine ⟨unreversePrism K, ?_, ?_, ?_, ?_⟩
  · rw [unreversePrism_endpoint]
    change (SSet.opFunctorCompOpFunctorIso.app (vertexFiber p b)).inv ≫
      SSet.opFunctor.map (prismEndpoint 1 _ ≫ K) ≫ _ = _
    rw [hk1, Functor.map_comp]
    rfl
  · rw [unreversePrism_endpoint]
    change (SSet.opFunctorCompOpFunctorIso.app (vertexFiber p b)).inv ≫
      SSet.opFunctor.map (prismEndpoint 0 _ ≫ K) ≫ _ = _
    rw [hk0]
    rfl
  · have hkb : K ≫ SSet.opFunctor.map p =
        fst (Δ[1] : SSet.{u}) (vertexFiber p b).op ≫
          (SSet.yonedaEquiv.symm (edgeOp e).edge : (Δ[1] : SSet.{u}) ⟶ B.op) := by
      exact congrArg (fun f : (Δ[1] : SSet.{u}) ⊗
        vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ⟶ B.op ↦
          ((Δ[1] : SSet.{u}) ◁ (vertexFiberOpIso p b).hom) ≫ f) hb
    rw [← unreversePrism_postcomp, hkb, unreversePrism_base]
  · apply unreversePrism_vertical_isCartesian p K
    intro v
    change IsCocartesianEdge (SSet.opFunctor.map p)
      (H.app (Opposite.op ⦋1⦌) (_, (vertexFiberOpIso p b).hom.app _
        (PinchedHom.constant v 1)))
    rw [pinchedConstant_map]
    exact hc ((vertexFiberOpIso p b).hom.app _ v)

end
end SerrePositivity.InfinityCategories.HomotopyLimits

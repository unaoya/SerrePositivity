module

public import SerrePositivity.InfinityCategories.HomotopyLimits.YonedaIdentityNormalizedTransports
public import SerrePositivity.InfinityCategories.HomotopyLimits.YonedaEvaluationVertexTransport

/-!
概要：元の Yoneda の脚の恒等点評価を、同じ表現可能前層の反変輸送点へ比較する。
方針：元の Yoneda 一単体を正規化し、同じ恒等点の二方向の標準輸送比較へ接続する。
規約：元の辺・元の Yoneda の高次作用・同じ評価点を保持する。
使われ方：有限余積の各脚についての、Yoneda 評価の第一変数の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {C : SSet.{u}} [Quasicategory C] (f : (Δ[1] : SSet.{u}) ⟶ C)
local notation "x₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
local notation "y₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)

/-- 元の Yoneda の辺を、同じ二つの表現可能前層の関手頂点で正規化する。 -/
def yonedaRepresentableNativeEdge :
    SSet.Edge (functorVertex (representablePresheafInfinity x₀))
      (functorVertex (representablePresheafInfinity y₀)) := by
  let e := (SSet.Edge.ofTruncated homotopyIntervalEdge).map f
  have he : e.edge = SSet.yonedaEquiv f := by
    change f.app (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge =
      f.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
    apply congrArg (f.app (Opposite.op ⦋1⦌))
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  let t : SSet.Edge (X := (SSet.uliftFunctor.{u + 1, u}).obj C)
      (ULift.up x₀) (ULift.up y₀) :=
    ⟨ULift.up (SSet.yonedaEquiv f), congrArg ULift.up (he ▸ e.src_eq),
      congrArg ULift.up (he ▸ e.tgt_eq)⟩
  let h := t.map (yonedaInfinityMap C)
  exact ⟨h.edge, h.src_eq.trans (yonedaInfinityMap_vertex x₀),
    h.tgt_eq.trans (yonedaInfinityMap_vertex y₀)⟩

/-- 正規化した辺は、元の Yoneda の同じ一単体そのもの。 -/
lemma yonedaRepresentableNativeEdge_edge :
    (yonedaRepresentableNativeEdge f).edge =
      (yonedaInfinityMap C).app (Opposite.op ⦋1⦌) (ULift.up (SSet.yonedaEquiv f)) := rfl

/-- 元の Yoneda の辺を始点で評価すると、同じ恒等点輸送の元の底辺を回収する。 -/
lemma yonedaRepresentableNativeEdge_evaluated :
    functorEdgeAt
      (intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge (yonedaRepresentableNativeEdge f)))
      (ULift.up (SSet.opObjEquiv.symm x₀)) = yonedaIdentityNormalizedSourceEdge f := by
  have he : intervalMappingEdgeOfVertex
      (intervalMappingVertexOfEdge (yonedaRepresentableNativeEdge f)) =
      yonedaRepresentableNativeEdge f :=
    (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _
  rw [he]
  apply SSet.Edge.ext
  change (evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x₀))).app (Opposite.op ⦋1⦌)
    (yonedaRepresentableNativeEdge f).edge = (yonedaIdentityNormalizedSourceEdge f).edge
  rw [yonedaRepresentableNativeEdge_edge, yonedaIdentityNormalizedSourceEdge_edge]
  rfl

/-- 元の Yoneda の脚の恒等点像は、元の同じ表現可能前層の反変辺による輸送点と同型。 -/
def yonedaRepresentableNativeEdge_evaluationIso :
    VertexIso
      ((canonicalYonedaTransformationFiberEvaluation x₀ (representablePresheafInfinity y₀)).app
        (Opposite.op ⦋0⦌) (intervalMappingVertexOfEdge (yonedaRepresentableNativeEdge f)))
      (yonedaIdentityNormalizedTargetPoint f) := by
  have h := canonicalYonedaFiberEvaluation_vertexTransportIso x₀
    (representablePresheafInfinity y₀)
    (intervalMappingVertexOfEdge (yonedaRepresentableNativeEdge f))
  rw [yonedaRepresentableNativeEdge_evaluated] at h
  exact h ≪≫ yonedaIdentityNormalizedTransportsIso f

end SerrePositivity.InfinityCategories.HomotopyLimits

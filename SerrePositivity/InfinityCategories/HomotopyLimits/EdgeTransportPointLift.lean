module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialFiberEdgeTransport

/-!
概要：指定した transport の証人を fiber の点で評価し、全空間の実際の輸送辺を取り出す。
方針：prism の区間辺と定値 fiber 辺の直積を写し、両端と底の射影を計算する。
規約：既存の transport の選択を保持する。使われ方：貼った余錐の枝を span の実際の脚と結ぶ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 指定した transport による点の像へ、底の辺を厳密に被覆する実際の辺が存在。 -/
lemma exists_edge_of_transport_point {E B : SSet.{u}} (p : E ⟶ B)
    {a b : B _⦋0⦌} (e : B.Edge a b)
    (f : vertexFiber p a ⟶ vertexFiber p b) (hf : IsEdgeTransport p e f)
    (v : (vertexFiber p a) _⦋0⦌) :
    ∃ k : E.Edge v.val (f.app (Opposite.op ⦋0⦌) v).val, (k.map p).edge = e.edge := by
  obtain ⟨H, h₀, h₁, hH, _⟩ := hf
  let t := (homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
    (X := (truncation 2).obj (vertexFiber p a)) v)).map ((truncation 2).map H)
  have hs := congrArg (fun q : vertexFiber p a ⟶ E ↦ q.app (Opposite.op ⦋0⦌) v) h₀
  have ht := congrArg (fun q : vertexFiber p a ⟶ E ↦ q.app (Opposite.op ⦋0⦌) v) h₁
  let k : E.Edge v.val (f.app (Opposite.op ⦋0⦌) v).val :=
    SSet.Edge.ofTruncated ⟨t.edge, t.src_eq.trans hs, t.tgt_eq.trans ht⟩
  refine ⟨k, ?_⟩
  have h := congrArg (fun q : (Δ[1] : SSet.{u}) ⊗ vertexFiber p a ⟶ B ↦
    q.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 Δ[1]), PinchedHom.constant v 1)) hH
  change p.app (Opposite.op ⦋1⦌) (H.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (𝟙 Δ[1]), PinchedHom.constant v 1)) =
      (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 Δ[1])) at h
  rw [pinchedConstant_one] at h
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro t
    fin_cases t <;> rfl
  change p.app (Opposite.op ⦋1⦌) (H.app (Opposite.op ⦋1⦌)
    (homotopyIntervalEdge.edge, (SSet.Truncated.Edge.id
      (X := (truncation 2).obj (vertexFiber p a)) v).edge)) = e.edge
  rw [← hi]
  exact h.trans (SSet.yonedaEquiv_symm_app_id e.edge)

end
end SerrePositivity.InfinityCategories.HomotopyLimits

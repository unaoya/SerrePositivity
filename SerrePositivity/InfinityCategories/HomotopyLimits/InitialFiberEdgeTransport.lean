module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialFiberPostcomposition
public import SerrePositivity.InfinityCategories.F1.Transport.EdgeTransport

/-!
概要：始対象を持つ left fibration の fiber の Hom 表示は、端点を指定した実際の transport に自然。
方針：transport の prism を指定した fiber の頂点で評価し、全空間の辺の後合成の式を使う。
規約：選んだ transport とその証人をそのまま使い、別の同値な transport に置き換えない。
使われ方：span の終点へ輸送した部分余錐の境界の連結成分を、合成三角形で比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
  (c : E _⦋0⦌) (hc : IsInitialVertex c)

/-- transport が fiber の Hom 表示に及ぼす作用は、指定した底の辺との後合成。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_transport {a b : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b)
    (f : vertexFiber p a ⟶ vertexFiber p b) (hf : IsEdgeTransport p e f)
    (v : (vertexFiber p a) _⦋0⦌) :
    leftFibrationInitialFiberPiZeroEquiv p c hc a (SSet.π₀.mk v) ≫
        SSet.Truncated.HomotopyCategory.homMk e =
      leftFibrationInitialFiberPiZeroEquiv p c hc b (SSet.mapπ₀ f (SSet.π₀.mk v)) := by
  obtain ⟨H, h₀, h₁, hH, _⟩ := hf
  let t := (homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
    (X := (truncation 2).obj (vertexFiber p a)) v)).map ((truncation 2).map H)
  have hs := congrArg (fun q : vertexFiber p a ⟶ E ↦ q.app (Opposite.op ⦋0⦌) v) h₀
  have ht := congrArg (fun q : vertexFiber p a ⟶ E ↦ q.app (Opposite.op ⦋0⦌) v) h₁
  let k : E.Edge v.val (f.app (Opposite.op ⦋0⦌) v).val :=
    SSet.Edge.ofTruncated ⟨t.edge, t.src_eq.trans hs, t.tgt_eq.trans ht⟩
  have ha : p.app (Opposite.op ⦋0⦌) v.val = a := v.property.trans (pinchedConstant_zero a)
  have hb : p.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) v).val = b :=
    (f.app (Opposite.op ⦋0⦌) v).property.trans (pinchedConstant_zero b)
  have hk : (initialFiberTransportProjection p k a b ha hb).toTruncated = e := by
    apply SSet.Truncated.Edge.ext
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
  have h := leftFibrationInitialFiberPiZeroEquiv_post_edgeAt p c hc k a b ha hb
  rw [hk] at h
  exact h

/-- Hom 表示に対する transport の後合成の式は、fiber の任意の連結成分で成り立つ。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_transport_component {a b : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b)
    (f : vertexFiber p a ⟶ vertexFiber p b) (hf : IsEdgeTransport p e f)
    (v : SSet.π₀ (vertexFiber p a)) :
    leftFibrationInitialFiberPiZeroEquiv p c hc a v ≫
        SSet.Truncated.HomotopyCategory.homMk e =
      leftFibrationInitialFiberPiZeroEquiv p c hc b (SSet.mapπ₀ f v) := by
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective v
  exact leftFibrationInitialFiberPiZeroEquiv_transport p c hc e f hf v

end
end SerrePositivity.InfinityCategories.HomotopyLimits

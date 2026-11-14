module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryKindValues
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleExchange

/-!
# 水平・垂直の交換による境界種類の移送

Berger–Fresse §2.2.7、M14 L09a。
既存のshuffleの方向交換と、辺の補集合による同じ境界判定を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 既存の四種類の水平・垂直を交換する。 -/
def BoundaryVertexKind.exchange : BoundaryVertexKind → BoundaryVertexKind
  | .horizontal => .vertical
  | .vertical => .horizontal
  | .mixed => .mixed
  | .isolated => .isolated

lemma BoundaryVertexKind.exchange_involutive :
    Function.Involutive BoundaryVertexKind.exchange := by intro b; cases b <;> rfl

/-- 同じ境界判定を、水平辺集合と全辺数だけの式として読む。 -/
def setBoundaryKind {N : ℕ} (s : Finset (Fin N)) (k : Fin (N + 1)) :
    BoundaryVertexKind :=
  if hN : 0 < N then
    if h0 : k.val = 0 then
      if (⟨0, hN⟩ : Fin N) ∈ s then .horizontal else .vertical
    else if hlast : k.val = N then
      if (⟨N - 1, by omega⟩ : Fin N) ∈ s then .horizontal else .vertical
    else
      let h : 0 < k.val ∧ k.val < N := ⟨by omega, by have hk := k.isLt; omega⟩
      if cornerLeftEdge k h ∈ s then
        if cornerRightEdge k h ∈ s then .horizontal else .mixed
      else if cornerRightEdge k h ∈ s then .mixed else .vertical
  else .isolated

lemma boundaryVertexKind_eq_setBoundaryKind {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) : boundaryVertexKind s k = setBoundaryKind s.val k := rfl

/-- C72：同じ位置で水平辺の補集合を取ると水平・垂直の種類を交換する。 -/
lemma setBoundaryKind_compl {N : ℕ} (s : Finset (Fin N)) (k : Fin (N + 1)) :
    setBoundaryKind sᶜ k = (setBoundaryKind s k).exchange := by
  unfold setBoundaryKind
  simp only [Finset.mem_compl]
  split_ifs <;> simp_all [BoundaryVertexKind.exchange]

/-- C73：全辺数の等式で位置を移送しても、同じ境界判定になる。 -/
lemma setBoundaryKind_map_finCongr {N N' : ℕ} (h : N = N') (s : Finset (Fin N))
    (k : Fin (N + 1)) :
    setBoundaryKind (s.map (finCongr h).toEmbedding) (Fin.cast (congrArg (· + 1) h) k) =
      setBoundaryKind s k := by
  cases h
  simp only [finCongr_refl, Equiv.refl_toEmbedding, Finset.map_refl, Fin.cast_refl, id_eq]

/-- C74：既存のshuffleの方向交換は、指定頂点の水平・垂直の種類を交換する。 -/
lemma boundaryVertexKind_exchange {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
    boundaryVertexKind s.exchange (Fin.cast (by omega : m + q + 1 = q + m + 1) k) =
      (boundaryVertexKind s k).exchange := by
  change setBoundaryKind (s.valᶜ.map (finCongr (Nat.add_comm m q)).toEmbedding)
    (Fin.cast (congrArg (· + 1) (Nat.add_comm m q)) k) = (setBoundaryKind s.val k).exchange
  rw [setBoundaryKind_map_finCongr, setBoundaryKind_compl]

end SerrePositivity.EInfinity.SimplexCuts

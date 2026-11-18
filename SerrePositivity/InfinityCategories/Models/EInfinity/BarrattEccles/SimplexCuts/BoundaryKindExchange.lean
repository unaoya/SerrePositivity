module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryKindValues
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleExchange

/-!
模型。文献の定義との比較は後で
# 水平・垂直の交換による境界種類の移送

Berger–Fresse §2.2.7、M14 L09a。
既存のshuffleの方向交換と、辺の補集合による同じ境界判定を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 既存の四種類の水平・垂直を交換する。 -/
def _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind.exchange : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind
  | .horizontal => .vertical
  | .vertical => .horizontal
  | .mixed => .mixed
  | .isolated => .isolated

lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind.exchange_involutive :
    Function.Involutive _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind.exchange := by intro b; cases b <;> rfl

/-- 同じ境界判定を、水平辺集合と全辺数だけの式として読む。 -/
def setBoundaryKind {N : ℕ} (s : Finset (Fin N)) (k : Fin (N + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind :=
  if hN : 0 < N then
    if h0 : k.val = 0 then
      if (⟨0, hN⟩ : Fin N) ∈ s then .horizontal else .vertical
    else if hlast : k.val = N then
      if (⟨N - 1, by omega⟩ : Fin N) ∈ s then .horizontal else .vertical
    else
      let h : 0 < k.val ∧ k.val < N := ⟨by omega, by have hk := k.isLt; omega⟩
      if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerLeftEdge k h ∈ s then
        if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge k h ∈ s then .horizontal else .mixed
      else if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge k h ∈ s then .mixed else .vertical
  else .isolated

lemma boundaryVertexKind_eq_setBoundaryKind {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (k : Fin (m + q + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind s.val k := rfl

/-- C72：同じ位置で水平辺の補集合を取ると水平・垂直の種類を交換する。 -/
lemma setBoundaryKind_compl {N : ℕ} (s : Finset (Fin N)) (k : Fin (N + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind sᶜ k = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind s k).exchange := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind
  simp only [Finset.mem_compl]
  split_ifs <;> simp_all [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind.exchange]

/-- C73：全辺数の等式で位置を移送しても、同じ境界判定になる。 -/
lemma setBoundaryKind_map_finCongr {N N' : ℕ} (h : N = N') (s : Finset (Fin N))
    (k : Fin (N + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind (s.map (finCongr h).toEmbedding) (Fin.cast (congrArg (· + 1) h) k) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind s k := by
  cases h
  simp only [finCongr_refl, Equiv.refl_toEmbedding, Finset.map_refl, Fin.cast_refl, id_eq]

/-- C74：既存のshuffleの方向交換は、指定頂点の水平・垂直の種類を交換する。 -/
lemma boundaryVertexKind_exchange {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s.exchange (Fin.cast (by omega : m + q + 1 = q + m + 1) k) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k).exchange := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind (s.valᶜ.map (finCongr (Nat.add_comm m q)).toEmbedding)
    (Fin.cast (congrArg (· + 1) (Nat.add_comm m q)) k) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind s.val k).exchange
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind_map_finCongr, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.setBoundaryKind_compl]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

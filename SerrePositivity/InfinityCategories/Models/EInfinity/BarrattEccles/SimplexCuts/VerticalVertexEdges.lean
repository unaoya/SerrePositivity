module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryKindValues

/-!
模型。文献の定義との比較は後で
# 垂直境界頂点の前後の垂直辺

Berger–Fresse §2.2.7、M14 L09a。
既存の始端・内部・終端の境界種類の計算を、指定された隣接辺へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C227の証明分割：垂直境界頂点から出る辺は水平辺集合に入らない。 -/
lemma vertical_kind_outgoing_not_mem {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (k : Fin (m + q + 1)) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .vertical)
    (e : Fin (m + q)) (he : e.castSucc = k) : e ∉ s.val := by
  have hN : 0 < m + q := by have := e.isLt; omega
  rw [← he] at hk
  by_cases h0 : e.val = 0
  · have he0 : e.castSucc = 0 := Fin.ext h0
    have heq : e = (⟨0, hN⟩ : Fin (m + q)) := Fin.ext h0
    rw [he0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_zero s hN] at hk
    by_contra hmem
    simp only [← heq, ite_eq_left hmem, reduceCtorEq] at hk
  · have hi : 0 < e.castSucc.val ∧ e.castSucc.val < m + q := by
      have := e.isLt
      change 0 < e.val ∧ e.val < m + q
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_interior s e.castSucc hi] at hk
    have hr : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge e.castSucc hi = e := Fin.ext rfl
    rw [hr] at hk
    by_contra hmem
    by_cases hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerLeftEdge e.castSucc hi ∈ s.val <;>
      simp only [hl, hmem, ite_true, ite_false, reduceCtorEq] at hk

/-- C228の証明分割：垂直境界頂点へ入る辺は水平辺集合に入らない。 -/
lemma vertical_kind_incoming_not_mem {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (k : Fin (m + q + 1)) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .vertical)
    (e : Fin (m + q)) (he : e.succ = k) : e ∉ s.val := by
  have hN : 0 < m + q := by have := e.isLt; omega
  rw [← he] at hk
  by_cases hlast : e.val + 1 = m + q
  · have helast : e.succ = Fin.last (m + q) := Fin.ext hlast
    have heq : (⟨m + q - 1, by omega⟩ : Fin (m + q)) = e := by
      apply Fin.ext
      change m + q - 1 = e.val
      omega
    rw [helast, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_last s hN] at hk
    by_contra hmem
    simp only [heq, ite_eq_left hmem, reduceCtorEq] at hk
  · have hi : 0 < e.succ.val ∧ e.succ.val < m + q := by
      have := e.isLt
      change 0 < e.val + 1 ∧ e.val + 1 < m + q
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_interior s e.succ hi] at hk
    have hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerLeftEdge e.succ hi = e := by
      apply Fin.ext
      change e.val + 1 - 1 = e.val
      omega
    rw [hl] at hk
    by_contra hmem
    by_cases hr : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge e.succ hi ∈ s.val <;>
      simp only [hmem, hr, ite_true, ite_false, reduceCtorEq] at hk

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

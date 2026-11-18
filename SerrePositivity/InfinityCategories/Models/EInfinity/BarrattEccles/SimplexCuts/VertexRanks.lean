module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.FiberRanks

/-!
模型。文献の定義との比較は後で
# 面番号と先行する色の個数の一致

Berger–Fresse §2.2.7、M14 L09a。
色の列の先頭部分の長さを有限集合の濃度へ変え、境界面の番号と照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C31：色を選んだ先頭部分の長さは、その色の先行位置の数。 -/
lemma selectColor_take_ofFn_length {r N : ℕ} {β : Type*} (f : Fin N → Fin r × β)
    (c : Fin r) (k : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c ((List.ofFn f).take k)).length =
      (Finset.univ.filter (fun i => i.val < k ∧ (f i).1 = c)).card := by
  induction N generalizing k with
  | zero => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor]
  | succ N ih =>
    cases k with
    | zero => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor]
    | succ k =>
      have hc : (Finset.univ.filter (fun i : Fin (N + 1) =>
          i.val < k + 1 ∧ (f i).1 = c)).card =
          (if (f 0).1 = c then 1 else 0) +
          (Finset.univ.filter (fun i : Fin N => i.val < k ∧ (f i.succ).1 = c)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ,
          Fin.val_zero, Nat.zero_lt_succ, true_and, Fin.val_succ, Nat.add_lt_add_iff_right]
      rw [List.ofFn_succ, List.take_succ_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor_cons, hc]
      by_cases h : (f 0).1 = c <;> simp [h, ih, Nat.add_comm]

/-- C32：経路の先行同色数を、色のfiberの濃度で表す。 -/
lemma vertexRank_eq_card {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r)
    (c : Fin r) (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s v c k = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v c).filter (fun i => i < k)).card := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor_take_ofFn_length]
  congr 1
  ext i
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

/-- C33：先行同色数は、出力の実際の面番号と一致。 -/
lemma vertexRank_colorPositionEquiv {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u a + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s u.val a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u ⟨a, j⟩) = j.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank_eq_card, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv_rank]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

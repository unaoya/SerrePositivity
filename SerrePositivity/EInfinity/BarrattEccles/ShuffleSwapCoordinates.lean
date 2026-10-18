module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwap

/-!
# 隣接交換が変えない経路の頂点

概要：Berger–Fresse §1.1.3 の混合角の交換で、角の頂点以外の座標は変わらないことを示す。
方針：隣接辺 a,b の交換が、b 番目以外の接頭区間を保つことを数え上げで示す。
規約：辺の番号 b は交換される二辺の間の頂点の番号でもある。
使われ方：その頂点を除く境界面が二つの経路で一致することを導く。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：隣接辺の交換は中間の頂点以外の接頭区間を保つ（Berger–Fresse §1.1.3）。
方針：交換する端点の場合だけを分け、閾値が両端の間にないことを使う。
規約：頂点 k の番号が b と異なることを要求する。
使われ方：交換後の水平・垂直座標を元の座標と比較する。 -/
lemma swap_adjacent_lt_iff {N : ℕ} (a b : Fin N) (hab : b.val = a.val + 1)
    (k : Fin (N + 1)) (hk : k.val ≠ b.val) (x : Fin N) :
    (Equiv.swap a b x).val < k.val ↔ x.val < k.val := by
  by_cases hxa : x = a
  · subst x
    rw [Equiv.swap_apply_left]
    omega
  · by_cases hxb : x = b
    · subst x
      rw [Equiv.swap_apply_right]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- 概要：隣接辺の交換は中間以外の接頭区間に含まれる集合の濃度を保つ（Berger–Fresse §1.1.3）。
方針：交換後のフィルタを交換前のフィルタの像と同定する。
規約：集合が水平辺か垂直辺かは問わない。
使われ方：二つの経路の座標の一致を一つの計算から得る。 -/
lemma card_filter_map_swap {N : ℕ} (a b : Fin N) (hab : b.val = a.val + 1)
    (k : Fin (N + 1)) (hk : k.val ≠ b.val) (t : Finset (Fin N)) :
    ((t.map (Equiv.swap a b).toEmbedding).filter (fun x => x.val < k.val)).card =
      (t.filter (fun x => x.val < k.val)).card := by
  have h : (t.map (Equiv.swap a b).toEmbedding).filter (fun x => x.val < k.val) =
      (t.filter (fun x => x.val < k.val)).map (Equiv.swap a b).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_swap]
    rw [swap_adjacent_lt_iff a b hab k hk x]
  rw [h, Finset.card_map]

/-- 概要：隣接交換後の水平座標は中間の頂点以外で変わらない（Berger–Fresse §1.1.3）。
方針：水平辺の接頭区間内の個数が保存されることを使う。
規約：辺の向きが異なるという仮定は不要。
使われ方：混合角の頂点を除いた面の水平座標を比較する。 -/
lemma ShufflePath.horizontal_swapSteps {p q : ℕ} (s : ShufflePath p q)
    (a b : Fin (p + q)) (hab : b.val = a.val + 1) (k : Fin (p + q + 1))
    (hk : k.val ≠ b.val) : (s.swapSteps a b).horizontal k = s.horizontal k := by
  apply Fin.ext
  exact card_filter_map_swap a b hab k hk s.val

/-- 概要：隣接交換後の垂直座標は中間の頂点以外で変わらない（Berger–Fresse §1.1.3）。
方針：垂直辺の集合も同じ互換で動くことと接頭区間の個数の保存を使う。
規約：交換する辺が同じ向きの場合にも成立する。
使われ方：混合角の頂点を除いた面の垂直座標を比較する。 -/
lemma ShufflePath.vertical_swapSteps {p q : ℕ} (s : ShufflePath p q)
    (a b : Fin (p + q)) (hab : b.val = a.val + 1) (k : Fin (p + q + 1))
    (hk : k.val ≠ b.val) : (s.swapSteps a b).vertical k = s.vertical k := by
  apply Fin.ext
  change ((s.swapSteps a b).valᶜ.filter (fun x => x.val < k.val)).card =
    (s.valᶜ.filter (fun x => x.val < k.val)).card
  rw [s.swapSteps_compl a b]
  exact card_filter_map_swap a b hab k hk s.valᶜ

end SerrePositivity.EInfinity.BarrattEccles

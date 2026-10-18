module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalDeletion

/-!
# 一辺の削除前後の経路の座標

概要：Berger–Fresse §1.1.3 の同方向の境界面の比較に必要な、辺の削除前後の接頭辺数を求める。
方針：辺 a を削除した経路の頂点 k を、元の頂点 a+1 を飛ばす写像で移す。
規約：削除辺を含む集合では通過後の個数が一つ増え、含まない集合では変わらない。
使われ方：水平面と垂直面を一つ小さい shuffle と同定する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：一辺の削除に伴う辺と頂点の昇順移送は接頭区間を保つ（Berger–Fresse §1.1.3）。
方針：辺 a と頂点 a+1 のそれぞれを飛ばす場合分けを整数の不等式に直す。
規約：j は削除後の辺、k は削除後の頂点。
使われ方：削除後の辺の個数を元の接頭区間で数える。 -/
lemma succAbove_edge_lt_vertex_iff {N : ℕ} (a : Fin (N + 1)) (j : Fin N)
    (k : Fin (N + 1)) :
    (a.succAbove j).val < (a.succ.succAbove k).val ↔ j.val < k.val := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ] <;> omega

/-- 概要：削除位置は移送した頂点がその位置を通過したときだけ接頭区間に入る（Berger–Fresse §1.1.3）。
方針：頂点 a+1 を飛ばす写像の二つの場合を計算する。
規約：辺 a の所属は a<k で判定する。
使われ方：水平辺の挿入に伴う個数の増分を計算する。 -/
lemma deleted_edge_lt_vertex_iff {N : ℕ} (a : Fin (N + 1)) (k : Fin (N + 1)) :
    a.val < (a.succ.succAbove k).val ↔ a.val < k.val := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ]
  omega

/-- 概要：空けた辺位置の後方へ移す操作は対応する接頭辺数を保つ（Berger–Fresse §1.1.3）。
方針：有限集合の map と filter を交換し、辺・頂点の移送の不等式を使う。
規約：辺 a は集合に追加しない。
使われ方：削除した辺と異なる向きの座標の保存を示す。 -/
lemma filter_map_succAbove_card {N : ℕ} (s : Finset (Fin N)) (a : Fin (N + 1))
    (k : Fin (N + 1)) :
    ((s.map (Fin.succAboveOrderEmb a).toEmbedding).filter
      (fun x => x.val < (a.succ.succAbove k).val)).card =
      (s.filter (fun j => j.val < k.val)).card := by
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro j _
  exact succAbove_edge_lt_vertex_iff a j k

/-- 概要：一辺の挿入で接頭辺数は通過した場合にだけ一つ増える（Berger–Fresse §1.1.3）。
方針：挿入辺の filter の所属を判定し、残りの辺には map の個数の保存を使う。
規約：値の増分は自然数の 0 または 1。
使われ方：削除辺と同じ向きの経路座標の変化を求める。 -/
lemma insertPosition_filter_card {N : ℕ} (s : Finset (Fin N)) (a : Fin (N + 1))
    (k : Fin (N + 1)) :
    ((insertPosition s a).filter (fun x => x.val < (a.succ.succAbove k).val)).card =
      (s.filter (fun j => j.val < k.val)).card + if a.val < k.val then 1 else 0 := by
  have ha : a ∉ s.map (Fin.succAboveOrderEmb a).toEmbedding := by
    rintro h
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
    exact Fin.succAbove_ne a j hj
  have haf : a ∉ (s.map (Fin.succAboveOrderEmb a).toEmbedding).filter
      (fun x => x.val < (a.succ.succAbove k).val) := fun h => ha (Finset.mem_filter.mp h).1
  rw [insertPosition, Finset.filter_insert]
  by_cases hk : a.val < k.val
  · rw [ite_eq_left ((deleted_edge_lt_vertex_iff a k).2 hk), Finset.card_insert_of_notMem haf,
      filter_map_succAbove_card, ite_eq_left hk]
  · rw [ite_eq_right (fun h => hk ((deleted_edge_lt_vertex_iff a k).1 h)),
      filter_map_succAbove_card, ite_eq_right hk]
    rfl

/-- 概要：含まれる辺の削除では元の接頭辺数は通過後に一つ多い（Berger–Fresse §1.1.3）。
方針：削除後に同じ辺を挿入し直す公式へ接頭辺数の公式を適用する。
規約：削除辺 a の集合への所属を仮定する。
使われ方：水平辺を削除した際の水平座標、または垂直辺を削除した際の垂直座標を比較する。 -/
lemma erasePosition_filter_card_of_mem {N : ℕ} (s : Finset (Fin (N + 1)))
    (a : Fin (N + 1)) (ha : a ∈ s) (k : Fin (N + 1)) :
    (s.filter (fun x => x.val < (a.succ.succAbove k).val)).card =
      ((erasePosition s a).filter (fun j => j.val < k.val)).card +
        if a.val < k.val then 1 else 0 := by
  have h := insertPosition_filter_card (erasePosition s a) a k
  rw [insertPosition_erasePosition s a ha] at h
  exact h

/-- 概要：含まれない辺の削除では接頭辺数は変わらない（Berger–Fresse §1.1.3）。
方針：削除後の集合を元へ戻した像が元の集合に等しいことを使う。
規約：削除辺 a は集合に属さない。
使われ方：削除した辺と異なる向きの経路座標を比較する。 -/
lemma erasePosition_filter_card_of_notMem {N : ℕ} (s : Finset (Fin (N + 1)))
    (a : Fin (N + 1)) (ha : a ∉ s) (k : Fin (N + 1)) :
    (s.filter (fun x => x.val < (a.succ.succAbove k).val)).card =
      ((erasePosition s a).filter (fun j => j.val < k.val)).card := by
  have h := filter_map_succAbove_card (erasePosition s a) a k
  rw [map_erasePosition, Finset.erase_eq_of_notMem ha] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles

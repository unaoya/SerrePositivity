module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalDeletion

/-!
# 先頭の辺の削除と接頭辺数

概要：Berger–Fresse §1.1.3 の始端の面の比較に使う先頭辺の削除公式を証明する。
方針：全ての辺を一つ後ろへ移す像と、先頭の辺を加える insert を区別して数える。
規約：元の頂点 k+1 と削除後の頂点 k の接頭辺数を比較する。
使われ方：最初の辺の向きに応じて第一または第二の入力の最初の面を同定する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：全辺を一つ後ろへ移すと接頭区間の閾値も一つ増える（Berger–Fresse §1.1.3）。
方針：map と filter を交換し、自然数の両辺の後続による不等式の保存を使う。
規約：閾値 k は任意の自然数。
使われ方：削除する先頭辺と異なる向きの座標を比較する。 -/
lemma map_first_filter_card {N : ℕ} (s : Finset (Fin N)) (k : ℕ) :
    ((s.map (Fin.succAboveOrderEmb (0 : Fin (N + 1))).toEmbedding).filter
      (fun x => x.val < k + 1)).card = (s.filter (fun x => x.val < k)).card := by
  rw [Finset.filter_map, Finset.card_map]
  congr 1

/-- 概要：先頭に辺を挿入すると全ての非空の接頭区間で個数が一つ増える（Berger–Fresse §1.1.3）。
方針：後ろへ移した辺の像が先頭を含まないことを使い insert の濃度を求める。
規約：元の k+1 の接頭区間と挿入前の k の接頭区間を比較する。
使われ方：削除する先頭辺と同じ向きの座標を比較する。 -/
lemma insert_first_filter_card {N : ℕ} (s : Finset (Fin N)) (k : ℕ) :
    ((insertPosition s 0).filter (fun x => x.val < k + 1)).card =
      (s.filter (fun x => x.val < k)).card + 1 := by
  have ha : (0 : Fin (N + 1)) ∉ s.map (Fin.succAboveOrderEmb 0).toEmbedding := by
    rintro h
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
    exact Fin.succAbove_ne 0 j hj
  have haf : (0 : Fin (N + 1)) ∉ (s.map (Fin.succAboveOrderEmb 0).toEmbedding).filter
      (fun x => x.val < k + 1) := fun h => ha (Finset.mem_filter.mp h).1
  rw [insertPosition, Finset.filter_insert]
  erw [ite_eq_left (Nat.zero_lt_succ k)]
  rw [Finset.card_insert_of_notMem haf, map_first_filter_card]

/-- 概要：集合に属する先頭辺を削除すると接頭辺数が一つ減る（Berger–Fresse §1.1.3）。
方針：先頭への挿入と削除の逆性に接頭辺数の公式を適用する。
規約：元の集合に 0 が属することを要求する。
使われ方：始端の面で削除される入力の座標を一つ進める。 -/
lemma erase_first_filter_card_of_mem {N : ℕ} (s : Finset (Fin (N + 1))) (h₀ : 0 ∈ s)
    (k : ℕ) : (s.filter (fun x => x.val < k + 1)).card =
      ((erasePosition s 0).filter (fun x => x.val < k)).card + 1 := by
  have h := insert_first_filter_card (erasePosition s 0) k
  rw [insertPosition_erasePosition s 0 h₀] at h
  exact h

/-- 概要：集合に属さない先頭辺を削除しても対応する接頭辺数は変わらない（Berger–Fresse §1.1.3）。
方針：削除後の集合を後ろへ移した像が元の集合であることを使う。
規約：元の集合に 0 が属さないことを要求する。
使われ方：始端の面で削除されない入力の座標を保存する。 -/
lemma erase_first_filter_card_of_notMem {N : ℕ} (s : Finset (Fin (N + 1))) (h₀ : 0 ∉ s)
    (k : ℕ) : (s.filter (fun x => x.val < k + 1)).card =
      ((erasePosition s 0).filter (fun x => x.val < k)).card := by
  have h := map_first_filter_card (erasePosition s 0) k
  rw [map_erasePosition, Finset.erase_eq_of_notMem h₀] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles

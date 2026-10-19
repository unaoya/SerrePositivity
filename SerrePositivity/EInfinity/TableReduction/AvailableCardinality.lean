module

public import SerrePositivity.EInfinity.TableReduction.BlockWords

/-!
# 除外数と置換行の利用可能長

概要：Berger–Fresse §1.4.4 の除外を解いた後の利用可能長を計算する。
方針：元の行を除外値と残る値に分け、置換行が全ての値を一度ずつ含むことを使う。
規約：除外リストは重複を持たない。
使われ方：最後の行で解放値が必ず選択範囲に入ることを示す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

/-- 概要：除外値と利用可能値に分けた長さの和は元の行長（BF §1.4.4）。
方針：元のリストで帰納し、所属判定で二つの filter を分ける。
規約：元の行や除外状態の重複を許す。
使われ方：置換行の利用可能長を除外した値の数から求める。 -/
lemma available_length_add_removed_filter {α : Type*} [DecidableEq α]
    (removed row : List α) :
    (available removed row).length + (row.filter (fun x => x ∈ removed)).length = row.length := by
  induction row with
  | nil => rfl
  | cons a row ih =>
    by_cases ha : a ∈ removed <;> simp [available, ha] at ih ⊢ <;> omega

/-- 概要：置換行の利用可能長と除外長の和は arity（BF §1.4.4）。
方針：除外部分は除外リストそのものの並べ替えであることを示す。
規約：除外リストの重複のなさを要求する。
使われ方：抽出後の状態の長さから次の行の利用可能数を評価する。 -/
lemma available_vertexRow_length_add {n m : ℕ} (w : Fin m → Equiv.Perm (Fin n))
    (i : Fin m) (removed : List (Fin n)) (hn : removed.Nodup) :
    (available removed (vertexRow w i)).length + removed.length = n := by
  have hp : ((vertexRow w i).filter (fun x => x ∈ removed)).Perm removed := by
    apply (List.perm_ext_iff_of_nodup ((vertexRow_nodup w i).filter _) hn).mpr
    intro a
    simp only [List.mem_filter, mem_vertexRow, true_and, decide_eq_true_eq]
  have hs := available_length_add_removed_filter removed (vertexRow w i)
  rw [hp.length_eq] at hs
  simpa only [vertexRow, List.length_ofFn] using hs

/-- 概要：除外されていない一文字を除外に加えると利用可能長は一つ減る（BF §1.4.4）。
方針：二つの重複のない状態の長さの公式を比較する。
規約：a は除外リストに属さない。
使われ方：逆対応で a の除外を解いた状態の一文字の余裕を示す。 -/
lemma available_vertexRow_release_length {n m : ℕ} (w : Fin m → Equiv.Perm (Fin n))
    (i : Fin m) (removed : List (Fin n)) (hn : removed.Nodup) (a : Fin n) (ha : a ∉ removed) :
    (available removed (vertexRow w i)).length =
      (available (removed ++ [a]) (vertexRow w i)).length + 1 := by
  have hnew : (removed ++ [a]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hn, by simp, ?_⟩
    intro x hx y hy he
    have hya : y = a := List.mem_singleton.mp hy
    have hxa : x = a := he.trans hya
    exact ha (hxa ▸ hx)
  have hs := available_vertexRow_length_add w i removed hn
  have ht := available_vertexRow_length_add w i (removed ++ [a]) hnew
  simp only [List.length_append, List.length_singleton] at ht
  omega

/-- 概要：元の利用可能長を取り尽くす行では解放値が延長選択に入る（BF §1.4.4）。
方針：解放後の利用可能長は一つ増え、延長選択が全利用可能行となることを使う。
規約：解放値は元の除外に新たに加えられた一文字。
使われ方：最初に影響を受ける後続行の探索の最終行の分岐を閉じる。 -/
lemma released_value_mem_extended_take {n m : ℕ} (w : Fin m → Equiv.Perm (Fin n))
    (i : Fin m) (removed : List (Fin n)) (hn : removed.Nodup) (a : Fin n) (ha : a ∉ removed)
    (r : ℕ) (hr : (available (removed ++ [a]) (vertexRow w i)).length = r) :
    a ∈ (available removed (vertexRow w i)).take (r + 1) := by
  have hl := available_vertexRow_release_length w i removed hn a ha
  rw [hr] at hl
  have he : (available removed (vertexRow w i)).take (r + 1) =
      available removed (vertexRow w i) := List.take_of_length_le (by omega)
  rw [he]
  simp only [available, List.mem_filter, decide_eq_true_eq]
  exact ⟨mem_vertexRow w i a, ha⟩

end SerrePositivity.EInfinity.TableReduction

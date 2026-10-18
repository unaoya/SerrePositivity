module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSign

/-!
# shuffle の辺位置の削除と挿入

概要：Berger–Fresse §1.1.3 の境界計算に使う辺位置の削除と挿入を構成する。
方針：一つの位置を除く昇順埋め込み succAbove によって辺集合を移す。
規約：削除の位置は Fin(N+1)、削除後の位置は Fin N で表す。
使われ方：同方向の辺を縮めた経路と、一つ小さい shuffle を対応づける。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：辺集合から指定位置を削除し、残りの位置番号を詰める（Berger–Fresse §1.1.3）。
方針：指定位置を飛ばす昇順埋め込みの逆像を取る。
規約：削除位置が集合に属さない場合も定義する。
使われ方：shuffle の水平辺または垂直辺を一つ削除する。 -/
def erasePosition {N : ℕ} (s : Finset (Fin (N + 1))) (a : Fin (N + 1)) : Finset (Fin N) :=
  Finset.univ.filter (fun j => a.succAbove j ∈ s)

/-- 概要：位置を削除した後の所属は succAbove によって判定する（Berger–Fresse §1.1.3）。
方針：有限集合のフィルタの定義を評価する。
規約：削除位置そのものは像に現れない。
使われ方：削除・挿入の逆性と座標の計算に用いる。 -/
@[simp] lemma mem_erasePosition {N : ℕ} (s : Finset (Fin (N + 1)))
    (a : Fin (N + 1)) (j : Fin N) : j ∈ erasePosition s a ↔ a.succAbove j ∈ s := by
  simp [erasePosition]

/-- 概要：位置の削除で集合の濃度は通常の erase と同じになる（Berger–Fresse §1.1.3）。
方針：succAbove による残りの位置の全単射を濃度の比較に使う。
規約：削除位置が属するかどうかに依存しない等式。
使われ方：水平辺を削除した後の水平辺数を保証する。 -/
lemma erasePosition_card {N : ℕ} (s : Finset (Fin (N + 1))) (a : Fin (N + 1)) :
    (erasePosition s a).card = (s.erase a).card := by
  apply Finset.card_bij (fun j _ => a.succAbove j)
  · intro j hj
    exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne a j, (mem_erasePosition s a j).mp hj⟩
  · intro j _ k _ h
    exact Fin.succAbove_right_injective h
  · intro x hx
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hx).1
    exact ⟨j, (mem_erasePosition s a j).mpr (Finset.mem_erase.mp hx).2, rfl⟩

/-- 概要：指定位置に辺を一つ挿入する（Berger–Fresse §1.1.3）。
方針：元の位置を succAbove で移してから指定位置を加える。
規約：挿入された位置は必ず集合に属する。
使われ方：水平辺を一つ増やす経路を構成する。 -/
def insertPosition {N : ℕ} (s : Finset (Fin N)) (a : Fin (N + 1)) : Finset (Fin (N + 1)) :=
  insert a (s.map (Fin.succAboveOrderEmb a).toEmbedding)

/-- 概要：挿入された位置は挿入後の辺集合に属する（Berger–Fresse §1.1.3）。
方針：有限集合の insert の所属を使う。
規約：元の集合の条件は不要である。
使われ方：指定された水平辺を持つ経路を構成する。 -/
@[simp] lemma mem_insertPosition {N : ℕ} (s : Finset (Fin N)) (a : Fin (N + 1)) :
    a ∈ insertPosition s a := Finset.mem_insert_self _ _

/-- 概要：挿入によって辺数は一つ増える（Berger–Fresse §1.1.3）。
方針：succAbove の像は挿入位置を含まないため insert の濃度公式を使う。
規約：空の辺集合にも成立する。
使われ方：挿入した経路の水平辺数を計算する。 -/
lemma insertPosition_card {N : ℕ} (s : Finset (Fin N)) (a : Fin (N + 1)) :
    (insertPosition s a).card = s.card + 1 := by
  have ha : a ∉ s.map (Fin.succAboveOrderEmb a).toEmbedding := by
    rintro h
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
    exact Fin.succAbove_ne a j hj
  rw [insertPosition, Finset.card_insert_of_notMem ha, Finset.card_map]

/-- 概要：辺を挿入してからその位置を削除すると元に戻る（Berger–Fresse §1.1.3）。
方針：succAbove の単射性と挿入位置を避ける性質を使う。
規約：削除は位置番号を詰める操作も含む。
使われ方：辺の削除による shuffle の添字替えの逆性を示す。 -/
@[simp] lemma erasePosition_insertPosition {N : ℕ} (s : Finset (Fin N))
    (a : Fin (N + 1)) : erasePosition (insertPosition s a) a = s := by
  ext j
  simp only [mem_erasePosition, insertPosition, Finset.mem_insert,
    Fin.succAbove_ne, false_or]
  exact Finset.mem_map' (Fin.succAboveOrderEmb a).toEmbedding

/-- 概要：属する辺を削除してから同じ位置に挿入すると元に戻る（Berger–Fresse §1.1.3）。
方針：削除位置自身と、それ以外の succAbove の像に属する位置に分ける。
規約：削除位置が元の集合に属することを要求する。
使われ方：小さい shuffle と指定された辺を持つ大きい経路の対応を示す。 -/
lemma insertPosition_erasePosition {N : ℕ} (s : Finset (Fin (N + 1)))
    (a : Fin (N + 1)) (ha : a ∈ s) : insertPosition (erasePosition s a) a = s := by
  ext x
  by_cases hx : x = a
  · subst x
    simp [ha]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hx
    simp only [insertPosition, Finset.mem_insert, Fin.succAbove_ne, false_or]
    erw [Finset.mem_map' (Fin.succAboveOrderEmb a).toEmbedding]
    exact mem_erasePosition s a j

end SerrePositivity.EInfinity.BarrattEccles

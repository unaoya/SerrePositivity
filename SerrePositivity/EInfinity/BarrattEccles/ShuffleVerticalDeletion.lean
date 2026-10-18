module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDeletePosition

/-!
# 垂直辺の削除による shuffle の対応

概要：Berger–Fresse §1.1.3 の垂直辺の削除を shuffle 経路の同値として構成する。
方針：垂直辺の挿入では水平辺を succAbove で移すだけとし、その逆を辺位置の削除で与える。
規約：垂直辺数 q+1 の経路の指定垂直辺を削除すると、水平辺数は変わらない。
使われ方：垂直な同方向の境界面を小さい shuffle の有限和へ添字替えする。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：空けた位置を削除すると元の辺集合に戻る（Berger–Fresse §1.1.3）。
方針：succAbove の像に対する所属とその単射性を使う。
規約：空けた位置は辺集合に加えない。
使われ方：垂直辺の挿入の左逆を証明する。 -/
@[simp] lemma erasePosition_map_succAbove {N : ℕ} (s : Finset (Fin N))
    (a : Fin (N + 1)) : erasePosition (s.map (Fin.succAboveOrderEmb a).toEmbedding) a = s := by
  ext j
  rw [mem_erasePosition]
  exact Finset.mem_map' (Fin.succAboveOrderEmb a).toEmbedding

/-- 概要：位置を削除して残った位置へ戻した集合は通常の erase と一致する（Berger–Fresse §1.1.3）。
方針：削除位置とそれ以外の succAbove の像の位置に分けて所属を比較する。
規約：削除位置が集合に属さない場合には元の集合に一致する。
使われ方：垂直辺の挿入の右逆を証明する。 -/
lemma map_erasePosition {N : ℕ} (s : Finset (Fin (N + 1))) (a : Fin (N + 1)) :
    (erasePosition s a).map (Fin.succAboveOrderEmb a).toEmbedding = s.erase a := by
  ext x
  by_cases hx : x = a
  · subst x
    have ha : a ∉ (erasePosition s a).map (Fin.succAboveOrderEmb a).toEmbedding := by
      rintro h
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
      exact Fin.succAbove_ne a j hj
    exact iff_of_false ha (by simp)
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hx
    erw [Finset.mem_map' (Fin.succAboveOrderEmb a).toEmbedding]
    simp only [mem_erasePosition, Finset.mem_erase]
    constructor
    · intro h
      exact ⟨Fin.succAbove_ne a j, h⟩
    · exact And.right

/-- 概要：指定位置に垂直辺を持つ大きい経路と小さい経路の同値（Berger–Fresse §1.1.3）。
方針：水平辺集合を succAbove で移し、逆向きには指定位置を削除する。
規約：大きい経路での a は水平辺集合に属さない。
使われ方：垂直辺を削除する境界項の添字替えの基礎となる。 -/
def verticalInsertionEquiv (p q : ℕ) (a : Fin (p + (q + 1))) :
    ShufflePath p q ≃ {s : ShufflePath p (q + 1) // a ∉ s.val} where
  toFun s := ⟨⟨s.val.map (Fin.succAboveOrderEmb a).toEmbedding, by
      rw [Finset.card_map]; exact s.property⟩, by
    rintro h
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
    exact Fin.succAbove_ne a j hj⟩
  invFun s := ⟨erasePosition s.val.val a, by
    rw [erasePosition_card, Finset.erase_eq_of_notMem s.property]
    exact s.val.property⟩
  left_inv s := by
    apply Subtype.ext
    exact erasePosition_map_succAbove s.val a
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    change (erasePosition s.val.val a).map (Fin.succAboveOrderEmb a).toEmbedding = s.val.val
    rw [map_erasePosition, Finset.erase_eq_of_notMem s.property]

end SerrePositivity.EInfinity.BarrattEccles

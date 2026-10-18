module

public import SerrePositivity.EInfinity.BarrattEccles.ShufflePaths

/-!
# shuffle の辺の所属と座標の増分

概要：Berger–Fresse §1.1.3 の格子経路の辺の向きを座標の増分と結びつける。
方針：接頭区間を一位置増やしたときの辺数の変化を所属で計算する。
規約：水平辺は水平辺集合への所属、垂直辺は非所属で表す。
使われ方：同方向の隣接辺を縮めた境界面の座標を決める。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：接頭区間の終端を一つ進めると、そこに属する辺がある場合だけ個数が増える（Berger–Fresse §1.1.3）。
方針：一位置広いフィルタを insert または元のフィルタとして表す。
規約：辺番号の値に対する自然数の不等式で述べる。
使われ方：経路の水平・垂直の増分を具体的に判定する。 -/
lemma prefix_count_succ {N : ℕ} (s : Finset (Fin N)) (i : Fin N) :
    (s.filter (fun x => x.val < i.val + 1)).card =
      (s.filter (fun x => x.val < i.val)).card + if i ∈ s then 1 else 0 := by
  by_cases hi : i ∈ s
  · have hset : s.filter (fun x => x.val < i.val + 1) =
        insert i (s.filter (fun x => x.val < i.val)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hxS, hlt⟩
        by_cases hx : x = i
        · exact Or.inl hx
        · have hne : x.val ≠ i.val := fun h => hx (Fin.ext h)
          exact Or.inr ⟨hxS, by omega⟩
      · rintro (hx | ⟨hxS, hlt⟩)
        · subst x
          exact ⟨hi, Nat.lt_succ_self _⟩
        · exact ⟨hxS, by omega⟩
    have hn : i ∉ s.filter (fun x => x.val < i.val) := by simp
    rw [hset, Finset.card_insert_of_notMem hn, ite_eq_left hi]
  · have hset : s.filter (fun x => x.val < i.val + 1) =
        s.filter (fun x => x.val < i.val) := by
      ext x
      simp only [Finset.mem_filter]
      have hx : x ∈ s → x.val ≠ i.val := by
        intro hx h
        exact hi (Fin.ext h ▸ hx)
      constructor
      · rintro ⟨hxS, hlt⟩
        exact ⟨hxS, by have hne := hx hxS; omega⟩
      · rintro ⟨hxS, hlt⟩
        exact ⟨hxS, by omega⟩
    rw [hset, ite_eq_right hi]
    rfl

/-- 概要：水平辺では水平座標が一つ増え、垂直座標は変わらない（Berger–Fresse §1.1.3）。
方針：水平辺数の増分を求め、座標和が頂点番号に等しいことを使う。
規約：i.castSucc と i.succ が辺の始点と終点。
使われ方：連続する水平辺を削除した際の面の比較に用いる。 -/
lemma ShufflePath.step_of_mem {p q : ℕ} (s : ShufflePath p q) (i : Fin (p + q))
    (hi : i ∈ s.val) :
    (s.horizontal i.succ).val = (s.horizontal i.castSucc).val + 1 ∧
      s.vertical i.succ = s.vertical i.castSucc := by
  have hx := prefix_count_succ s.val i
  rw [ite_eq_left hi] at hx
  change (s.horizontal i.succ).val = (s.horizontal i.castSucc).val + 1 at hx
  refine ⟨hx, Fin.ext ?_⟩
  have h₀ := s.coordinate_sum i.castSucc
  have h₁ := s.coordinate_sum i.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h₀ h₁
  omega

/-- 概要：垂直辺では水平座標は変わらず、垂直座標が一つ増える（Berger–Fresse §1.1.3）。
方針：水平辺数の増分が零であることと座標和の公式を使う。
規約：垂直辺は水平辺集合への非所属で指定する。
使われ方：連続する垂直辺を削除した際の面の比較に用いる。 -/
lemma ShufflePath.step_of_notMem {p q : ℕ} (s : ShufflePath p q) (i : Fin (p + q))
    (hi : i ∉ s.val) :
    s.horizontal i.succ = s.horizontal i.castSucc ∧
      (s.vertical i.succ).val = (s.vertical i.castSucc).val + 1 := by
  have hx := prefix_count_succ s.val i
  rw [ite_eq_right hi] at hx
  change (s.horizontal i.succ).val = (s.horizontal i.castSucc).val + 0 at hx
  have hx' : s.horizontal i.succ = s.horizontal i.castSucc := Fin.ext hx
  refine ⟨hx', ?_⟩
  have h₀ := s.coordinate_sum i.castSucc
  have h₁ := s.coordinate_sum i.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h₀ h₁
  omega

end SerrePositivity.EInfinity.BarrattEccles

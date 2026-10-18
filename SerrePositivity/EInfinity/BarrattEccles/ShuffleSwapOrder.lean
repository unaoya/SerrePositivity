module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSign

/-!
# 隣接交換と昇順列挙

概要：Berger–Fresse §1.1.3 の shuffle の境界で現れる隣接交換を昇順列挙と比較する。
方針：交換する二点を両方含まない部分集合では隣接交換が狭義単調であることを使う。
規約：辺の位置 a と b は b=a+1 を満たす。
使われ方：水平辺と垂直辺の交換で shuffle の signature が反転することを導く。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：隣接交換は両端を同時に含まない部分集合の順序を保つ（Berger–Fresse §1.1.3）。
方針：交換の二端点に一致する場合だけを分け、隣接性で間の点がないことを使う。
規約：有限順序 Fin N の部分集合で述べる。
使われ方：交換後の水平辺・垂直辺の昇順列挙を計算する。 -/
lemma swap_adjacent_strictMonoOn {N : ℕ} (a b : Fin N) (hab : b.val = a.val + 1)
    (s : Finset (Fin N)) (hs : ¬ (a ∈ s ∧ b ∈ s)) :
    StrictMonoOn (Equiv.swap a b) (s : Set (Fin N)) := by
  intro x hx y hy hxy
  by_cases hxa : x = a
  · subst x
    have hya : y ≠ a := ne_of_gt hxy
    have hyb : y ≠ b := by
      intro h
      exact hs ⟨hx, h ▸ hy⟩
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hya hyb]
    have hne : y.val ≠ b.val := fun h => hyb (Fin.ext h)
    change a.val < y.val at hxy
    change b.val < y.val
    omega
  · by_cases hxb : x = b
    · subst x
      have hyb : y ≠ b := ne_of_gt hxy
      have hya : y ≠ a := by
        intro h
        have hv := congrArg Fin.val h
        change b.val < y.val at hxy
        omega
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hya hyb]
      change b.val < y.val at hxy
      change a.val < y.val
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
      by_cases hya : y = a
      · subst y
        rw [Equiv.swap_apply_left]
        change x.val < a.val at hxy
        change x.val < b.val
        omega
      · by_cases hyb : y = b
        · subst y
          rw [Equiv.swap_apply_right]
          have hne : x.val ≠ a.val := fun h => hxa (Fin.ext h)
          change x.val < b.val at hxy
          change x.val < a.val
          omega
        · rwa [Equiv.swap_apply_of_ne_of_ne hya hyb]

/-- 概要：順序を保つ置換で有限集合を移すと、昇順列挙もその置換で移る（Berger–Fresse §1.1.3）。
方針：移した列の狭義単調性と、全ての値が像集合に入ることから列挙の一意性を使う。
規約：部分集合上での狭義単調性だけを仮定する。
使われ方：隣接交換で shuffle 置換全体を比較する。 -/
lemma orderEmbOfFin_map_perm {N k : ℕ} (s : Finset (Fin N)) (hs : s.card = k)
    (e : Equiv.Perm (Fin N)) (he : StrictMonoOn e (s : Set (Fin N))) :
    (fun i : Fin k => (s.map e.toEmbedding).orderEmbOfFin (by simpa using hs) i) =
      (fun i => e (s.orderEmbOfFin hs i)) := by
  apply funext
  intro i
  have h := Finset.orderEmbOfFin_unique (s := s.map e.toEmbedding) (by simpa using hs)
    (f := fun j => e (s.orderEmbOfFin hs j))
    (fun j => Finset.mem_map.mpr ⟨_, s.orderEmbOfFin_mem hs j, rfl⟩)
    (fun _ _ hij => he (s.orderEmbOfFin_mem hs _) (s.orderEmbOfFin_mem hs _)
      ((s.orderEmbOfFin hs).strictMono hij))
  exact (congrFun h i).symm

end SerrePositivity.EInfinity.BarrattEccles

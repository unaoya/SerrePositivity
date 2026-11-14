module

public import SerrePositivity.EInfinity.SimplexCuts.IntervalExtrema

/-!
# 削除した経路の対応する区間の右端

Berger–Fresse §2.2.7、M14 L09a。
座標の対応と残るfiberの全射性から、同じ垂直座標で読む右端を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C173：座標を保つ対応でfiberが全て残れば、区間の右端の垂直座標は一致。 -/
lemma hi_eq_of_coordinate_cover {m n q : ℕ} (s : Cut m q) (t : Cut n q)
    (ρ : Fin (n + q + 1) → Fin (m + q + 1)) (φ : Fin (n + 1) → Fin (m + 1))
    (hφ : Function.Injective φ)
    (hh : ∀ j, s.horizontal (ρ j) = φ (t.horizontal j))
    (hv : ∀ j, s.vertical (ρ j) = t.vertical j)
    (i : Fin (n + 1))
    (hcover : ∀ j, s.horizontal j = φ i → ∃ k, ρ k = j) :
    hi t i = hi s (φ i) := by
  let j := (intervalPositions s (φ i)).max' (intervalPositions_nonempty s (φ i))
  have hj : s.horizontal j = φ i := horizontal_hi_vertex s (φ i)
  obtain ⟨k, hk⟩ := hcover j hj
  apply hi_eq_of_bound t i _ k
  · apply hφ
    rw [← hh k, hk]
    exact hj
  · rw [← hv k, hk]
    rfl
  · intro l hl
    rw [← hv l]
    apply vertical_le_hi s (φ i) (ρ l)
    rw [hh l, hl]

end SerrePositivity.EInfinity.SimplexCuts

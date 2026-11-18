module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalExtrema

/-!
模型。文献の定義との比較は後で
# 削除した経路の対応する区間の右端

Berger–Fresse §2.2.7、M14 L09a。
座標の対応と残るfiberの全射性から、同じ垂直座標で読む右端を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C173：座標を保つ対応でfiberが全て残れば、区間の右端の垂直座標は一致。 -/
lemma hi_eq_of_coordinate_cover {m n q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut n q)
    (ρ : Fin (n + q + 1) → Fin (m + q + 1)) (φ : Fin (n + 1) → Fin (m + 1))
    (hφ : Function.Injective φ)
    (hh : ∀ j, s.horizontal (ρ j) = φ (t.horizontal j))
    (hv : ∀ j, s.vertical (ρ j) = t.vertical j)
    (i : Fin (n + 1))
    (hcover : ∀ j, s.horizontal j = φ i → ∃ k, ρ k = j) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (φ i) := by
  let j := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s (φ i)).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s (φ i))
  have hj : s.horizontal j = φ i := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex s (φ i)
  obtain ⟨k, hk⟩ := hcover j hj
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_bound t i _ k
  · apply hφ
    rw [← hh k, hk]
    exact hj
  · rw [← hv k, hk]
    rfl
  · intro l hl
    rw [← hv l]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s (φ i) (ρ l)
    rw [hh l, hl]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

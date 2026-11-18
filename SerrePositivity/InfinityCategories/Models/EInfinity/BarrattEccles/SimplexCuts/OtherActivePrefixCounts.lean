module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ActiveHorizontalFilterCounts

/-!
模型。文献の定義との比較は後で
# 元の他色の先行活動頂点数と水平位置の和

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同色以外では同じ水平区間を除き、元の水平位置の前後で数える。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の他色の前後は、同じ水平位置の前後（BF §2.2.4）。 -/
lemma other_before_iff_horizontal_before {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (w : Fin (m + 1) → Fin r) (k : Fin r) (p : Fin (m + 1)) (hp : w p = k)
    (x j : Fin (m + q + 1)) (hx : s.horizontal x = p) :
    (j < x ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s w j ≠ k) ↔ (s.horizontal j < p ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s w j ≠ k) := by
  constructor
  · rintro ⟨hj, hn⟩
    have hh := s.horizontal.monotone hj.le
    rw [hx] at hh
    refine ⟨lt_of_le_of_ne hh ?_, hn⟩
    intro he
    apply hn
    change w (s.horizontal j) = k
    rw [he, hp]
  · rintro ⟨hh, hn⟩
    refine ⟨?_, hn⟩
    by_contra hj
    have hr := s.horizontal.monotone (le_of_not_gt hj)
    rw [hx] at hr
    exact (not_le_of_gt hh) hr

/-- 元の先行他色数は、同じ水平区間長の重み付き和（BF §2.2.6）。 -/
lemma other_active_prefix_card_eq_weighted {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (w : Fin (m + 1) → Fin r) (k : Fin r) (p : Fin (m + 1)) (hp : w p = k)
    (x : Fin (m + q + 1)) (hx : s.horizontal x = p) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s w).filter (fun z => z < x ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s w z ≠ k)).card =
      ∑ j : Fin (m + 1), if j < p ∧ w j ≠ k then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w j else 0 := by
  have he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s w).filter (fun z => z < x ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s w z ≠ k) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s w).filter (fun z => s.horizontal z < p ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s w z ≠ k) := by
    ext z
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.other_before_iff_horizontal_before s w k p hp x z hx)
  rw [he]
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.active_filter_horizontal_card s w (fun j => j < p ∧ w j ≠ k)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

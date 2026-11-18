module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalDeletedMaxima
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalActiveMaxima
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalIntervalThresholds
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalDeletionExponents
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentDeletions

/-!
模型。文献の定義との比較は後で
# 垂直削除による位置指数の差

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
残る活動区間の右端を読み、位置指数の差を同じ語の末尾側のcaesura数へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C229：同じ語の位置指数の差は、削除区間以後のcaesuraの個数。 -/
lemma positionExponent_vertical_deleted_coordinates {m q r : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + (q + 1) + 1)) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent t v +
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v).filter (fun i => s.horizontal k ≤ i)).card := by
  have hterm : ∀ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i + if s.horizontal k ≤ i then 1 else 0 := by
    intro i hci
    have hmax := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_vertex_ne_vertical_of_caesura s v k hk i (Finset.mem_filter.mp hci).2
    have hx := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_vertical_deleted_coordinates s t k hh hv i hmax
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.succAbove_val_eq] at hx
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i = (if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i < (s.vertical k).val then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i else _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i + 1) at hx
    have hthreshold := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_vertex_le_hi_iff s k hk i
    by_cases hlt : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i < (s.vertical k).val
    · rw [ite_eq_left hlt] at hx
      have hnot : ¬s.horizontal k ≤ i := by rw [← hthreshold]; omega
      simpa only [ite_eq_right hnot, Nat.add_zero] using hx
    · rw [ite_eq_right hlt] at hx
      have hge : s.horizontal k ≤ i := by rw [← hthreshold]; omega
      simpa only [ite_eq_left hge] using hx
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent_eq_caesura_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent_eq_caesura_sum]
  calc
    (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i) =
        ∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i + if s.horizontal k ≤ i then 1 else 0) :=
      Finset.sum_congr rfl hterm
    _ = (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i) +
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v).filter (fun i => s.horizontal k ≤ i)).card := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

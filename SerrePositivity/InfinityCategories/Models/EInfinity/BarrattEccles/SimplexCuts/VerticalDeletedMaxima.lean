module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DeletedIntervalMaxima
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.StraightTraceFaces

/-!
模型。文献の定義との比較は後で
# 垂直削除で残る区間の右端

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
既存の右端の特徴付けを、同じ垂直削除の順序単射へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C226：削除しない右端は、指定された垂直座標の順序単射で比較できる。 -/
lemma hi_eq_of_vertical_deleted_coordinates {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (k : Fin (m + (q + 1) + 1))
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j))
    (i : Fin (m + 1))
    (hmax : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i) ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i = ((s.vertical k).succAbove ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i, by have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_le_q t i; omega⟩).val := by
  let js := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i)
  let jt := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions t i).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty t i)
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hmax
  have hji : t.horizontal j = i := by
    rw [← hh j, hj]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex s i
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_bound s i _ (k.succAbove jt)
  · exact (hh jt).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex t i)
  · rw [hv jt]
    rfl
  · intro l hl
    have hsmall : t.vertical j ≤ (⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i, by have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_le_q t i; omega⟩ : Fin (q + 1)) :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi t i j hji
    have hmon := (Fin.strictMono_succAbove (s.vertical k)).monotone hsmall
    have hvj := hv j
    rw [hj] at hvj
    calc
      (s.vertical l).val ≤ (s.vertical js).val := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s i l hl
      _ = ((s.vertical k).succAbove (t.vertical j)).val := congrArg Fin.val hvj
      _ ≤ ((s.vertical k).succAbove ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i, by have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_le_q t i; omega⟩).val := hmon

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

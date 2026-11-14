module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedIntervalMaxima
public import SerrePositivity.EInfinity.SimplexCuts.StraightTraceFaces

/-!
# 垂直削除で残る区間の右端

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
既存の右端の特徴付けを、同じ垂直削除の順序単射へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C226：削除しない右端は、指定された垂直座標の順序単射で比較できる。 -/
lemma hi_eq_of_vertical_deleted_coordinates {m q : ℕ} (s : Cut m (q + 1)) (t : Cut m q)
    (k : Fin (m + (q + 1) + 1))
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j))
    (i : Fin (m + 1))
    (hmax : (intervalPositions s i).max' (intervalPositions_nonempty s i) ≠ k) :
    hi s i = ((s.vertical k).succAbove ⟨hi t i, by have := hi_le_q t i; omega⟩).val := by
  let js := (intervalPositions s i).max' (intervalPositions_nonempty s i)
  let jt := (intervalPositions t i).max' (intervalPositions_nonempty t i)
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hmax
  have hji : t.horizontal j = i := by
    rw [← hh j, hj]
    exact horizontal_hi_vertex s i
  apply hi_eq_of_bound s i _ (k.succAbove jt)
  · exact (hh jt).trans (horizontal_hi_vertex t i)
  · rw [hv jt]
    rfl
  · intro l hl
    have hsmall : t.vertical j ≤ (⟨hi t i, by have := hi_le_q t i; omega⟩ : Fin (q + 1)) :=
      vertical_le_hi t i j hji
    have hmon := (Fin.strictMono_succAbove (s.vertical k)).monotone hsmall
    have hvj := hv j
    rw [hj] at hvj
    calc
      (s.vertical l).val ≤ (s.vertical js).val := vertical_le_hi s i l hl
      _ = ((s.vertical k).succAbove (t.vertical j)).val := congrArg Fin.val hvj
      _ ≤ ((s.vertical k).succAbove ⟨hi t i, by have := hi_le_q t i; omega⟩).val := hmon

end SerrePositivity.EInfinity.SimplexCuts

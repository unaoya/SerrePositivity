module

public import SerrePositivity.EInfinity.SimplexCuts.Signs

/-!
# 切断区間の両端の評価

Berger–Fresse §2.2.3–4、M14 L09a。
区間の最小・最大の垂直座標を、所属する頂点と上下界で特徴づける。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

lemma horizontal_lo_vertex {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
    s.horizontal ((intervalPositions s i).min' (intervalPositions_nonempty s i)) = i :=
  (Finset.mem_filter.mp ((intervalPositions s i).min'_mem (intervalPositions_nonempty s i))).2

lemma horizontal_hi_vertex {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
    s.horizontal ((intervalPositions s i).max' (intervalPositions_nonempty s i)) = i :=
  (Finset.mem_filter.mp ((intervalPositions s i).max'_mem (intervalPositions_nonempty s i))).2

/-- C05の評価：区間のどの頂点も左端より後にある。 -/
lemma lo_le_vertical {m q : ℕ} (s : Cut m q) (i : Fin (m + 1))
    (j : Fin (m + q + 1)) (hj : s.horizontal j = i) : lo s i ≤ (s.vertical j).val := by
  apply s.vertical.monotone
  exact (intervalPositions s i).min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

/-- C05の評価：区間のどの頂点も右端より前にある。 -/
lemma vertical_le_hi {m q : ℕ} (s : Cut m q) (i : Fin (m + 1))
    (j : Fin (m + q + 1)) (hj : s.horizontal j = i) : (s.vertical j).val ≤ hi s i := by
  apply s.vertical.monotone
  exact (intervalPositions s i).le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

/-- C05：左端は、達成される下界で特徴づけられる。 -/
lemma lo_eq_of_bound {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) (n : ℕ)
    (j : Fin (m + q + 1)) (hj : s.horizontal j = i) (hv : (s.vertical j).val = n)
    (hb : ∀ k, s.horizontal k = i → n ≤ (s.vertical k).val) : lo s i = n := by
  apply Nat.le_antisymm
  · exact hv ▸ lo_le_vertical s i j hj
  · exact hb _ (horizontal_lo_vertex s i)

/-- C06：右端は、達成される上界で特徴づけられる。 -/
lemma hi_eq_of_bound {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) (n : ℕ)
    (j : Fin (m + q + 1)) (hj : s.horizontal j = i) (hv : (s.vertical j).val = n)
    (hb : ∀ k, s.horizontal k = i → (s.vertical k).val ≤ n) : hi s i = n := by
  apply Nat.le_antisymm
  · exact hb _ (horizontal_hi_vertex s i)
  · exact hv ▸ vertical_le_hi s i j hj

lemma lo_le_q {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) : lo s i ≤ q :=
  Nat.le_of_lt_succ (s.vertical _).isLt

lemma hi_le_q {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) : hi s i ≤ q :=
  Nat.le_of_lt_succ (s.vertical _).isLt

end SerrePositivity.EInfinity.SimplexCuts

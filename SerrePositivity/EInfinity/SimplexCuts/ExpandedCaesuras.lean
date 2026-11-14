module

public import SerrePositivity.EInfinity.SimplexCuts.ColorIntervalDegrees

/-!
# 展開した色列のcaesuraと区間の符号次数

Berger–Fresse §2.2.3–4・§2.2.7、M14 L09a。
展開した色列には隣接反復があるので、Surjection.Wordとはせず関数のまま扱う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C100：展開色列の後続の同色は、同じ区間の後続頂点か元の語の後続の同色。 -/
lemma caesura_label_iff {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) (j : Fin (m + q + 1)) (hj : s.horizontal j = i) :
    Surjection.Caesura (label s v) j ↔
      j < (intervalPositions s i).max' (intervalPositions_nonempty s i) ∨
      Surjection.Caesura v i := by
  constructor
  · rintro ⟨k, hjk, hk⟩
    have hc : v (s.horizontal k) = v i := by simpa only [label, hj] using hk
    have hle : i ≤ s.horizontal k := by simpa only [hj] using s.horizontal.monotone hjk.le
    by_cases he : s.horizontal k = i
    · left
      have hm : k ∈ intervalPositions s i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      exact lt_of_lt_of_le hjk ((intervalPositions s i).le_max' k hm)
    · exact Or.inr ⟨s.horizontal k, lt_of_le_of_ne hle (Ne.symm he), hc⟩
  · rintro (h | ⟨l, hil, hl⟩)
    · refine ⟨(intervalPositions s i).max' (intervalPositions_nonempty s i), h, ?_⟩
      change v (s.horizontal _) = v (s.horizontal j)
      rw [horizontal_hi_vertex, hj]
    · obtain ⟨k, hk⟩ := s.horizontal_surjective l
      have hjk : j < k := by
        by_contra h
        have hb := s.horizontal.monotone (le_of_not_gt h)
        rw [hk, hj] at hb
        exact (not_le_of_gt hil) hb
      refine ⟨k, hjk, ?_⟩
      change v (s.horizontal k) = v (s.horizontal j)
      rw [hk, hj]
      exact hl

/-- C101：一つの区間の展開caesuraの個数は、その区間の符号次数。 -/
lemma interval_active_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) :
    ((intervalPositions s i).filter (Surjection.Caesura (label s v))).card =
      intervalLength s v i := by
  unfold intervalLength
  by_cases hc : Surjection.Caesura v i
  · rw [ite_eq_left hc]
    have hs : (intervalPositions s i).filter (Surjection.Caesura (label s v)) =
        intervalPositions s i := by
      apply Finset.filter_true_of_mem
      intro j hj
      exact (caesura_label_iff s v i j (Finset.mem_filter.mp hj).2).mpr (Or.inr hc)
    rw [hs, intervalPositions_card]
  · simp only [ite_eq_right hc, Nat.add_zero]
    have hs : (intervalPositions s i).filter (Surjection.Caesura (label s v)) =
        (intervalPositions s i).erase
          ((intervalPositions s i).max' (intervalPositions_nonempty s i)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hj, hca⟩
        have hl := ((caesura_label_iff s v i j (Finset.mem_filter.mp hj).2).mp hca).resolve_right hc
        exact ⟨ne_of_lt hl, hj⟩
      · rintro ⟨hne, hj⟩
        refine ⟨hj, (caesura_label_iff s v i j (Finset.mem_filter.mp hj).2).mpr (Or.inl ?_)⟩
        exact lt_of_le_of_ne ((intervalPositions s i).le_max' j hj) hne
    rw [hs, Finset.card_erase_of_mem
      ((intervalPositions s i).max'_mem (intervalPositions_nonempty s i)), intervalPositions_card]
    omega

end SerrePositivity.EInfinity.SimplexCuts

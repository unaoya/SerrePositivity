module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ColorIntervalDegrees

/-!
模型。文献の定義との比較は後で
# 展開した色列のcaesuraと区間の符号次数

Berger–Fresse §2.2.3–4・§2.2.7、M14 L09a。
展開した色列には隣接反復があるので、Surjection.Wordとはせず関数のまま扱う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C100：展開色列の後続の同色は、同じ区間の後続頂点か元の語の後続の同色。 -/
lemma caesura_label_iff {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) (j : Fin (m + q + 1)) (hj : s.horizontal j = i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) j ↔
      j < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i) ∨
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i := by
  constructor
  · rintro ⟨k, hjk, hk⟩
    have hc : v (s.horizontal k) = v i := by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label, hj] using hk
    have hle : i ≤ s.horizontal k := by simpa only [hj] using s.horizontal.monotone hjk.le
    by_cases he : s.horizontal k = i
    · left
      have hm : k ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      exact lt_of_lt_of_le hjk ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).le_max' k hm)
    · exact Or.inr ⟨s.horizontal k, lt_of_le_of_ne hle (Ne.symm he), hc⟩
  · rintro (h | ⟨l, hil, hl⟩)
    · refine ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i), h, ?_⟩
      change v (s.horizontal _) = v (s.horizontal j)
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex, hj]
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
lemma interval_active_card {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v))).card =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s v i := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength
  by_cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i
  · rw [ite_eq_left hc]
    have hs : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v)) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i := by
      apply Finset.filter_true_of_mem
      intro j hj
      exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesura_label_iff s v i j (Finset.mem_filter.mp hj).2).mpr (Or.inr hc)
    rw [hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_card]
  · simp only [ite_eq_right hc, Nat.add_zero]
    have hs : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v)) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).erase
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hj, hca⟩
        have hl := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesura_label_iff s v i j (Finset.mem_filter.mp hj).2).mp hca).resolve_right hc
        exact ⟨ne_of_lt hl, hj⟩
      · rintro ⟨hne, hj⟩
        refine ⟨hj, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesura_label_iff s v i j (Finset.mem_filter.mp hj).2).mpr (Or.inl ?_)⟩
        exact lt_of_le_of_ne ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).le_max' j hj) hne
    rw [hs, Finset.card_erase_of_mem
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).max'_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i)), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_card]
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

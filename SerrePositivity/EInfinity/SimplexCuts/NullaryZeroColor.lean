module

public import SerrePositivity.EInfinity.SimplexCuts.ColorOccurrenceBoundaries
public import SerrePositivity.EInfinity.SimplexCuts.IntervalCardinalities

/-!
# nullaryで消える指定色の同じ零次元区間

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §316。
元の色別位置・同じ水平射影・区間の両端を保って読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 零次元の色の出力には、元の語の一出現だけが属する（BF §2.2.6）。 -/
lemma outputDegree_zero_occurrenceCount {m q r : ℕ} (s : Cut m q)
    (w : Surjection.Word r (m + 1)) (k : Fin r) (h : outputDegree s w k = 0) :
    Surjection.occurrenceCount w.val k = 1 := by
  have hpos := Surjection.occurrenceCount_pos w k
  by_contra hne
  let i : Fin (Surjection.occurrenceCount w.val k) := ⟨0, hpos⟩
  let j : Fin (Surjection.occurrenceCount w.val k) := ⟨1, by omega⟩
  have hlt := colorOccurrenceLast_lt_first s w k i j (by change (0 : ℕ) < 1; omega)
  have hj := (colorOccurrenceFirst s w k j).isLt
  change (colorOccurrenceLast s w k i).val < (colorOccurrenceFirst s w k j).val at hlt
  omega

/-- 零次元の指定色の区間は元の同じ一頂点（BF §2.2.6）。 -/
lemma outputDegree_zero_hi_eq_lo {m q r : ℕ} (s : Cut m q)
    (w : Surjection.Word r (m + 1)) (k : Fin r) (h : outputDegree s w k = 0)
    (p : Fin (m + 1)) (hp : w.val p = k) : hi s p = lo s p := by
  have hsub : intervalPositions s p ⊆ colorPositions s w.val k := by
    intro j hj
    have he := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change w.val (s.horizontal j) = k
    rw [he, hp]
  have hc := Finset.card_le_card hsub
  rw [colorPositions_card_eq, h] at hc
  have hi := intervalPositions_card s p
  have hlo := lo_le_hi s p
  omega

/-- 元の零次元の色は、唯一の出現の同じ一頂点と同値（BF §2.2.6）。 -/
lemma outputDegree_zero_iff_unique_position_and_point {m q r : ℕ} (s : Cut m q)
    (w : Surjection.Word r (m + 1)) (k : Fin r) :
    outputDegree s w k = 0 ↔
      ∃ p : Fin (m + 1), w.val p = k ∧
        (∀ j : Fin (m + 1), w.val j = k → j = p) ∧ hi s p = lo s p := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := w.surjective k
    obtain ⟨y, hy⟩ := s.horizontal_surjective p
    have hm : y ∈ colorPositions s w.val k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change w.val (s.horizontal y) = k; rw [hy, hp]⟩
    have hc : (colorPositions s w.val k).card ≤ 1 := by rw [colorPositions_card_eq, h]
    refine ⟨p, hp, ?_, outputDegree_zero_hi_eq_lo s w k h p hp⟩
    intro j hj
    obtain ⟨z, hz⟩ := s.horizontal_surjective j
    have hmz : z ∈ colorPositions s w.val k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change w.val (s.horizontal z) = k; rw [hz, hj]⟩
    have he := Finset.card_le_one.mp hc z hmz y hm
    exact hz.symm.trans ((congrArg s.horizontal he).trans hy)
  · rintro ⟨p, hp, hu, hpoint⟩
    have he : colorPositions s w.val k = intervalPositions s p := by
      ext j
      simp only [colorPositions, intervalPositions, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        exact hu (s.horizontal j) hj
      · intro hj
        change w.val (s.horizontal j) = k
        rw [hj, hp]
    unfold outputDegree
    rw [he, intervalPositions_card, hpoint]
    omega

end SerrePositivity.EInfinity.SimplexCuts

module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ColorOccurrenceBoundaries
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalCardinalities

/-!
模型。文献の定義との比較は後で
# nullaryで消える指定色の同じ零次元区間

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §316。
元の色別位置・同じ水平射影・区間の両端を保って読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 零次元の色の出力には、元の語の一出現だけが属する（BF §2.2.6）。 -/
lemma outputDegree_zero_occurrenceCount {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin r) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s w k = 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount w.val k = 1 := by
  have hpos := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos w k
  by_contra hne
  let i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount w.val k) := ⟨0, hpos⟩
  let j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount w.val k) := ⟨1, by omega⟩
  have hlt := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorOccurrenceLast_lt_first s w k i j (by change (0 : ℕ) < 1; omega)
  have hj := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorOccurrenceFirst s w k j).isLt
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorOccurrenceLast s w k i).val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorOccurrenceFirst s w k j).val at hlt
  omega

/-- 零次元の指定色の区間は元の同じ一頂点（BF §2.2.6）。 -/
lemma outputDegree_zero_hi_eq_lo {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin r) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s w k = 0)
    (p : Fin (m + 1)) (hp : w.val p = k) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p := by
  have hsub : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s p ⊆ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s w.val k := by
    intro j hj
    have he := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change w.val (s.horizontal j) = k
    rw [he, hp]
  have hc := Finset.card_le_card hsub
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq, h] at hc
  have hi := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_card s p
  have hlo := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_hi s p
  omega

/-- 元の零次元の色は、唯一の出現の同じ一頂点と同値（BF §2.2.6）。 -/
lemma outputDegree_zero_iff_unique_position_and_point {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s w k = 0 ↔
      ∃ p : Fin (m + 1), w.val p = k ∧
        (∀ j : Fin (m + 1), w.val j = k → j = p) ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := w.surjective k
    obtain ⟨y, hy⟩ := s.horizontal_surjective p
    have hm : y ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s w.val k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change w.val (s.horizontal y) = k; rw [hy, hp]⟩
    have hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s w.val k).card ≤ 1 := by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq, h]
    refine ⟨p, hp, ?_, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_zero_hi_eq_lo s w k h p hp⟩
    intro j hj
    obtain ⟨z, hz⟩ := s.horizontal_surjective j
    have hmz : z ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s w.val k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change w.val (s.horizontal z) = k; rw [hz, hj]⟩
    have he := Finset.card_le_one.mp hc z hmz y hm
    exact hz.symm.trans ((congrArg s.horizontal he).trans hy)
  · rintro ⟨p, hp, hu, hpoint⟩
    have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s w.val k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s p := by
      ext j
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        exact hu (s.horizontal j) hj
      · intro hj
        change w.val (s.horizontal j) = k
        rw [hj, hp]
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_card, hpoint]
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

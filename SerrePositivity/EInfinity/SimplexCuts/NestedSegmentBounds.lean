module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveNestedCuts
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleExchange

/-!
# 二段切断から読む元の内側部分語の端点

Berger–Fresse §1.2.4・§2.2.6、M14 L12a。
元の色の順位区間の両端を、元の内側切断の縦fiberの両端へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の内側切断で、指定した外側出現に最初に属する内側位置（BF §2.2.6）。 -/
def nestedSegmentStart {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a))
    (j : Fin (Surjection.occurrenceCount v.val a)) : ℕ :=
  lo t.exchange (colorOccurrenceFirst s v a j)

/-- 元の内側切断で、指定した外側出現に最後に属する内側位置（BF §2.2.6）。 -/
def nestedSegmentEnd {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a))
    (j : Fin (Surjection.occurrenceCount v.val a)) : ℕ :=
  hi t.exchange (colorOccurrenceLast s v a j)

/-- C369：同じ部分語の始点は終点以下（BF §1.2.4・§2.2.6）。 -/
lemma nestedSegmentStart_le_end {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a)) (j : Fin (Surjection.occurrenceCount v.val a)) :
    nestedSegmentStart s v a t j ≤ nestedSegmentEnd s v a t j :=
  (lo_le_hi t.exchange _).trans (hi_monotone t.exchange (colorOccurrenceFirst_le_last s v a j))

/-- C370：同じ部分語の終点は元の内側の最後の位置以下（BF §1.2.4）。 -/
lemma nestedSegmentEnd_le {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a)) (j : Fin (Surjection.occurrenceCount v.val a)) :
    nestedSegmentEnd s v a t j ≤ l := hi_le_q t.exchange _

/-- C371：最初の出現の内側始点は零（BF §1.2.4）。 -/
lemma nestedSegmentStart_zero {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a)) (j : Fin (Surjection.occurrenceCount v.val a))
    (hj : j.val = 0) : nestedSegmentStart s v a t j = 0 := by
  have he : j = ⟨0, Surjection.occurrenceCount_pos v a⟩ := Fin.ext hj
  have hf : colorOccurrenceFirst s v a j = 0 := by
    apply Fin.ext
    simp only [he, colorOccurrenceFirst_zero, Fin.val_zero]
  unfold nestedSegmentStart
  rw [hf, lo_zero]

/-- C372：最後の出現の内側終点は元の最後の位置（BF §1.2.4）。 -/
lemma nestedSegmentEnd_last {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a)) (j : Fin (Surjection.occurrenceCount v.val a))
    (hj : j.val + 1 = Surjection.occurrenceCount v.val a) : nestedSegmentEnd s v a t j = l := by
  have he : colorOccurrenceLast s v a j = Fin.last (outputDegree s v a) :=
    Fin.ext (colorOccurrenceLast_top s v a j hj)
  unfold nestedSegmentEnd
  rw [he, hi_last]

/-- C373：隣の元の部分語は、同じ内側位置を端点に共有する（BF §1.2.4）。 -/
lemma nestedSegmentEnd_eq_start {m q r l : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (t : Cut l (outputDegree s v a))
    (j j' : Fin (Surjection.occurrenceCount v.val a)) (hj : j.val + 1 = j'.val) :
    nestedSegmentEnd s v a t j = nestedSegmentStart s v a t j' := by
  have hs := colorOccurrence_adjacent s v a j j' hj
  let i : Fin (outputDegree s v a) := ⟨(colorOccurrenceLast s v a j).val, by
    have hb := (colorOccurrenceFirst s v a j').isLt
    omega⟩
  have h0 : i.castSucc = colorOccurrenceLast s v a j := Fin.ext rfl
  have h1 : i.succ = colorOccurrenceFirst s v a j' := Fin.ext hs
  have h := hi_eq_lo_succ t.exchange i
  unfold nestedSegmentEnd nestedSegmentStart
  simpa only [h0, h1] using h

end SerrePositivity.EInfinity.SimplexCuts

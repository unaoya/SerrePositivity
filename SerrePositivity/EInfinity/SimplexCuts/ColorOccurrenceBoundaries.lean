module

public import SerrePositivity.EInfinity.SimplexCuts.ColorRankIntervals
public import SerrePositivity.EInfinity.Surjection.OccurrenceOrder

/-!
# 同じ色の出現順で並べた順位区間の端点

Berger–Fresse §1.2.4・§2.2.6、M14 L12a。
元の出現順と元の順位の被覆を使い、最初・最後・隣接する区間の順位を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C361：元の出現順は、指定色を持つ元の位置を全て列挙する（BF §1.2.4）。 -/
lemma occurrenceAt_exists {r l : ℕ} (v : Fin l → Fin r) (a : Fin r)
    (p : Fin l) (hp : v p = a) :
    ∃ j : Fin (Surjection.occurrenceCount v a), Surjection.occurrenceAt v a j = p := by
  have hm : p ∈ Surjection.occurrencePositions v a := by
    simp [Surjection.occurrencePositions, hp]
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
  refine ⟨⟨j.val, lt_of_lt_of_le j.isLt
    (le_of_eq (Surjection.occurrencePositions_length v a))⟩, ?_⟩
  exact hj

/-- 指定色の元の第j出現に属する最初の順位（BF §2.2.6）。 -/
def colorOccurrenceFirst {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) : Fin (outputDegree s v a + 1) :=
  colorIntervalFirst s v a (Surjection.occurrenceAt v.val a j)
    (Surjection.occurrenceAt_value v.val a j)

/-- 指定色の元の第j出現に属する最後の順位（BF §2.2.6）。 -/
def colorOccurrenceLast {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) : Fin (outputDegree s v a + 1) :=
  colorIntervalLast s v a (Surjection.occurrenceAt v.val a j)
    (Surjection.occurrenceAt_value v.val a j)

/-- C362：最初の順位は、同じ出現の区間に属する（BF §2.2.6）。 -/
lemma colorOccurrenceFirst_mem {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) :
    colorOccurrenceFirst s v a j ∈ colorIntervalRanks s v a (Surjection.occurrenceAt v.val a j) :=
  (colorIntervalRanks s v a _).min'_mem (colorIntervalRanks_nonempty s v a _
    (Surjection.occurrenceAt_value v.val a j))

/-- C363：最後の順位は、同じ出現の区間に属する（BF §2.2.6）。 -/
lemma colorOccurrenceLast_mem {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) :
    colorOccurrenceLast s v a j ∈ colorIntervalRanks s v a (Surjection.occurrenceAt v.val a j) :=
  (colorIntervalRanks s v a _).max'_mem (colorIntervalRanks_nonempty s v a _
    (Surjection.occurrenceAt_value v.val a j))

/-- C364：同じ出現の最初の順位は最後以下（BF §2.2.6）。 -/
lemma colorOccurrenceFirst_le_last {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a)) :
    colorOccurrenceFirst s v a j ≤ colorOccurrenceLast s v a j :=
  colorIntervalFirst_le_last s v a _ (Surjection.occurrenceAt_value v.val a j)

/-- C365：出現順が進むと、元の順位区間も厳密に後へ進む（BF §2.2.6）。 -/
lemma colorOccurrenceLast_lt_first {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r)
    (j j' : Fin (Surjection.occurrenceCount v.val a)) (hj : j < j') :
    colorOccurrenceLast s v a j < colorOccurrenceFirst s v a j' :=
  colorIntervalLast_lt_first s v a _ _ (Surjection.occurrenceAt_value v.val a j)
    (Surjection.occurrenceAt_value v.val a j') (Surjection.occurrenceAt_strictMono v.val a hj)

/-- C366：元の最初の出現の順位区間は零から始まる（BF §2.2.6）。 -/
lemma colorOccurrenceFirst_zero {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) :
    (colorOccurrenceFirst s v a ⟨0, Surjection.occurrenceCount_pos v a⟩).val = 0 := by
  let j0 : Fin (Surjection.occurrenceCount v.val a) := ⟨0, Surjection.occurrenceCount_pos v a⟩
  change (colorOccurrenceFirst s v a j0).val = 0
  obtain ⟨p, hp, hz⟩ := colorIntervalRanks_cover s v a 0
  obtain ⟨j, hj⟩ := occurrenceAt_exists v.val a p hp
  have hz' : 0 ∈ colorIntervalRanks s v a (Surjection.occurrenceAt v.val a j) := by
    simpa only [hj] using hz
  have he : j = j0 := by
    by_contra hne
    have hne' : j.val ≠ 0 := fun h => hne (Fin.ext h)
    have hlt : j0 < j := by change 0 < j.val; omega
    have hbad := colorIntervalRanks_ordered s v a _ _
      (Surjection.occurrenceAt_strictMono v.val a hlt) _ _
      (colorOccurrenceFirst_mem s v a j0) hz'
    have hbad' : (colorOccurrenceFirst s v a j0).val < 0 := hbad
    omega
  rw [he] at hz'
  have hle := (colorIntervalRanks s v a _).min'_le 0 hz'
  exact Nat.eq_zero_of_le_zero hle

/-- C367：元の最後の出現の順位区間は、出力の最後の順位で終わる（BF §2.2.6）。 -/
lemma colorOccurrenceLast_top {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (Surjection.occurrenceCount v.val a))
    (hj : j.val + 1 = Surjection.occurrenceCount v.val a) :
    (colorOccurrenceLast s v a j).val = outputDegree s v a := by
  obtain ⟨p, hp, hz⟩ := colorIntervalRanks_cover s v a (Fin.last (outputDegree s v a))
  obtain ⟨l, hl⟩ := occurrenceAt_exists v.val a p hp
  have hz' : Fin.last (outputDegree s v a) ∈
      colorIntervalRanks s v a (Surjection.occurrenceAt v.val a l) := by
    simpa only [hl] using hz
  have he : l = j := by
    by_contra hne
    have hne' : l.val ≠ j.val := fun h => hne (Fin.ext h)
    have hlt : l < j := by have h := l.isLt; change l.val < j.val; omega
    have hbad := colorIntervalRanks_ordered s v a _ _
      (Surjection.occurrenceAt_strictMono v.val a hlt) _ _ hz' (colorOccurrenceFirst_mem s v a j)
    have hbad' : outputDegree s v a < (colorOccurrenceFirst s v a j).val := hbad
    have hbound := (colorOccurrenceFirst s v a j).isLt
    omega
  rw [he] at hz'
  have hle := (colorIntervalRanks s v a _).le_max' (Fin.last (outputDegree s v a)) hz'
  have hbound := (colorOccurrenceLast s v a j).isLt
  change outputDegree s v a ≤ (colorOccurrenceLast s v a j).val at hle
  omega

/-- C368：隣の出現の元の順位区間には隙間がない（BF §2.2.6）。 -/
lemma colorOccurrence_adjacent {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (j j' : Fin (Surjection.occurrenceCount v.val a)) (hj : j.val + 1 = j'.val) :
    (colorOccurrenceLast s v a j).val + 1 = (colorOccurrenceFirst s v a j').val := by
  let f := colorOccurrenceLast s v a j
  let g := colorOccurrenceFirst s v a j'
  have hfg : f < g := colorOccurrenceLast_lt_first s v a j j' (by change j.val < j'.val; omega)
  by_contra hne
  have hgap : f.val + 1 < g.val := by have h := hfg; change f.val < g.val at h; omega
  let z : Fin (outputDegree s v a + 1) := ⟨f.val + 1, lt_trans hgap g.isLt⟩
  obtain ⟨p, hp, hz⟩ := colorIntervalRanks_cover s v a z
  obtain ⟨l, hl⟩ := occurrenceAt_exists v.val a p hp
  have hz' : z ∈ colorIntervalRanks s v a (Surjection.occurrenceAt v.val a l) := by
    simpa only [hl] using hz
  rcases lt_trichotomy l j with hlj | he | hjl
  · have hbad := colorIntervalRanks_ordered s v a _ _
      (Surjection.occurrenceAt_strictMono v.val a hlj) _ _ hz' (colorOccurrenceLast_mem s v a j)
    have hbad' : z.val < f.val := hbad
    dsimp only [z] at hbad'
    omega
  · subst l
    have hbad := (colorIntervalRanks s v a _).le_max' z hz'
    change z.val ≤ f.val at hbad
    dsimp only [z] at hbad
    omega
  · by_cases he : l = j'
    · subst l
      have hbad := (colorIntervalRanks s v a _).min'_le z hz'
      change g.val ≤ z.val at hbad
      dsimp only [z] at hbad
      omega
    · have hne' : l.val ≠ j'.val := fun h => he (Fin.ext h)
      have hlt : j' < l := by have h := hjl; change j.val < l.val at h; change j'.val < l.val; omega
      have hbad := colorIntervalRanks_ordered s v a _ _
        (Surjection.occurrenceAt_strictMono v.val a hlt) _ _ (colorOccurrenceFirst_mem s v a j') hz'
      have hbad' : g.val < z.val := hbad
      dsimp only [z] at hbad'
      omega

end SerrePositivity.EInfinity.SimplexCuts

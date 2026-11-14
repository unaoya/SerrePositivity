module

public import SerrePositivity.EInfinity.SimplexCuts.ColorIntervalRanks

/-!
# 元の色の順位を連続した閉区間として読む

Berger–Fresse §2.2.3–6、M14 L12a の分割の復元。
元の順位集合の最小・最大を使い、同じ水平座標の単調なfiberが閉区間であることを示す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の区間に属する最初の色の順位（BF §2.2.6）。 -/
def colorIntervalFirst {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) : Fin (outputDegree s v a + 1) :=
  (colorIntervalRanks s v a p).min' (colorIntervalRanks_nonempty s v a p hp)

/-- 元の区間に属する最後の色の順位（BF §2.2.6）。 -/
def colorIntervalLast {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) : Fin (outputDegree s v a + 1) :=
  (colorIntervalRanks s v a p).max' (colorIntervalRanks_nonempty s v a p hp)

/-- C358：同じ色の一つの区間の順位集合は、元の最初/最後の閉区間（BF §2.2.6）。 -/
lemma colorIntervalRanks_eq_Icc {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    colorIntervalRanks s v a p =
      Finset.Icc (colorIntervalFirst s v a p hp) (colorIntervalLast s v a p hp) := by
  ext j
  constructor
  · intro hj
    exact Finset.mem_Icc.mpr ⟨(colorIntervalRanks s v a p).min'_le j hj,
      (colorIntervalRanks s v a p).le_max' j hj⟩
  · intro hj
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hj
    let E := (colorPositions s v.val a).orderEmbOfFin (colorPositions_card_eq s v a)
    have h1 := s.horizontal.monotone (E.monotone hl)
    have h2 := s.horizontal.monotone (E.monotone hr)
    have hfirst : s.horizontal (E (colorIntervalFirst s v a p hp)) = p :=
      (Finset.mem_filter.mp ((colorIntervalRanks s v a p).min'_mem
        (colorIntervalRanks_nonempty s v a p hp))).2
    have hlast : s.horizontal (E (colorIntervalLast s v a p hp)) = p :=
      (Finset.mem_filter.mp ((colorIntervalRanks s v a p).max'_mem
        (colorIntervalRanks_nonempty s v a p hp))).2
    rw [hfirst] at h1
    rw [hlast] at h2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm h2 h1⟩

/-- C359：元の区間の最初の順位は最後以下（BF §2.2.6）。 -/
lemma colorIntervalFirst_le_last {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    colorIntervalFirst s v a p hp ≤ colorIntervalLast s v a p hp :=
  (colorIntervalRanks s v a p).min'_le _
    ((colorIntervalRanks s v a p).max'_mem (colorIntervalRanks_nonempty s v a p hp))

/-- C360：先の区間の最後の順位は、後の区間の最初より小さい（BF §2.2.6）。 -/
lemma colorIntervalLast_lt_first {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (hp : v.val p = a) (hp' : v.val p' = a) (hpp' : p < p') :
    colorIntervalLast s v a p hp < colorIntervalFirst s v a p' hp' :=
  colorIntervalRanks_ordered s v a p p' hpp' _ _
    ((colorIntervalRanks s v a p).max'_mem (colorIntervalRanks_nonempty s v a p hp))
    ((colorIntervalRanks s v a p').min'_mem (colorIntervalRanks_nonempty s v a p' hp'))

end SerrePositivity.EInfinity.SimplexCuts

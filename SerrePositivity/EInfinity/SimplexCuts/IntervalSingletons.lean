module

public import SerrePositivity.EInfinity.SimplexCuts.IntervalExtrema

/-!
# 零長の切断区間と一頂点のfiber

Berger–Fresse §2.2.7、M14 L09a。
係数の文字を削除する境界は、水平座標のfiberが一頂点になる区間から生じる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

lemma lo_le_hi {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) : lo s i ≤ hi s i :=
  lo_le_vertical s i _ (horizontal_hi_vertex s i)

/-- C47：区間のfiberが一頂点であることと、両端の垂直座標が一致することは同値。 -/
lemma intervalPositions_card_eq_one_iff {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
    (intervalPositions s i).card = 1 ↔ lo s i = hi s i := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
    simp only [lo, hi, hj, Finset.min'_singleton, Finset.max'_singleton]
  · intro h
    let j₀ := (intervalPositions s i).min' (intervalPositions_nonempty s i)
    apply Finset.card_eq_one.mpr
    refine ⟨j₀, ?_⟩
    ext j
    constructor
    · intro hj
      apply Finset.mem_singleton.mpr
      have hc := (Finset.mem_filter.mp hj).2
      apply s.vertex_injective
      apply Prod.ext
      · exact hc.trans (horizontal_lo_vertex s i).symm
      · apply Fin.ext
        have h₁ := lo_le_vertical s i j hc
        have h₂ := vertical_le_hi s i j hc
        change (s.vertical j).val = lo s i
        omega
    · intro hj
      exact Finset.mem_singleton.mp hj ▸
        (intervalPositions s i).min'_mem (intervalPositions_nonempty s i)

/-- C48：幾何学的長さ零は、一頂点のfiberの条件。 -/
lemma interval_gap_eq_zero_iff {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
    hi s i - lo s i = 0 ↔ (intervalPositions s i).card = 1 := by
  rw [intervalPositions_card_eq_one_iff]
  have h := lo_le_hi s i
  omega

end SerrePositivity.EInfinity.SimplexCuts
